#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <time.h>

typedef struct {
    int from, to;
    char promo;
} Move;

typedef struct {
    char b[64];
    int white_to_move;
    int castle_wk, castle_wq, castle_bk, castle_bq;
} Pos;

static unsigned long long zobrist_table[64][12];
static unsigned long long zobrist_black_to_move;
static unsigned long long zobrist_castle[4];
static int zobrist_ready = 0;

// Generates pseudo-random numbers using a linear congruential generator
// Used to initialize Zobrist hashing values for board states
static unsigned long long lcg_rand(unsigned long long *s) {
    *s = *s * 6364136223846793005ULL + 1442695040888963407ULL;
    return *s;
}

// Initializes all Zobrist hashing tables (piece positions, turn, castling)
// Needed for fast position comparison and repetition detection
static void zobrist_init(void) {
    if (zobrist_ready) {
        return;
    }

    unsigned long long s = 0xDEADBEEFCAFEBABEULL;

    for (int sq = 0; sq < 64; sq++) {
        for (int pc = 0; pc < 12; pc++) {
            zobrist_table[sq][pc] = lcg_rand(&s);
        }
    }

    zobrist_black_to_move = lcg_rand(&s);

    for (int i = 0; i < 4; i++) {
        zobrist_castle[i] = lcg_rand(&s);
    }

    zobrist_ready = 1;
}

// Converts a piece character into an index for Zobrist hashing
// Each piece type gets a unique index for hashing
static int piece_to_zi(char pc) {
    switch (pc) {
        case 'P': return 0;
        case 'N': return 1;
        case 'B': return 2;
        case 'R': return 3;
        case 'Q': return 4;
        case 'K': return 5;
        case 'p': return 6;
        case 'n': return 7;
        case 'b': return 8;
        case 'r': return 9;
        case 'q': return 10;
        case 'k': return 11;
    }
    return -1;
}

// Computes a unique hash for the current board position
// Used for detecting repeated positions and speeding up search
static unsigned long long compute_hash(const Pos *p) {
    unsigned long long h = 0;

    for (int i = 0; i < 64; i++) {
        int idx = piece_to_zi(p->b[i]);

        if (idx >= 0) {
            h ^= zobrist_table[i][idx];
        }
    }

    if (!p->white_to_move) {
        h ^= zobrist_black_to_move;
    }
    if (p->castle_wk) {
        h ^= zobrist_castle[0];
    }
    if (p->castle_wq) {
        h ^= zobrist_castle[1];
    }
    if (p->castle_bk) {
        h ^= zobrist_castle[2];
    }
    if (p->castle_bq) {
        h ^= zobrist_castle[3];
    }

    return h;
}

#define MAX_HISTORY 1024
static unsigned long long game_history[MAX_HISTORY];
static int game_history_len = 0;

// Counts how many times a position hash appears
// Used to detect repetition draws during the game/search
static int count_reps(unsigned long long hash, const unsigned long long *ss, int sl) {
    int c = 0;

    for (int i = 0; i < game_history_len; i++) {
        if (game_history[i] == hash) {
            c++;
        }
    }

    for (int i = 0; i < sl; i++) {
        if (ss[i] == hash) {
            c++;
        }
    }

    return c;
}

// Converts a square string like "e2" into a board index (0-63)
static int sq_index(const char *s) {
    return (s[1] - '1') * 8 + (s[0] - 'a');
}

// Converts a board index (0-63) back into a string like "e2"
static void index_to_sq(int idx, char out[3]) {
    out[0] = (char)('a' + (idx % 8));
    out[1] = (char)('1' + (idx / 8));
    out[2] = 0;
}

// Returns 1 if the piece is white, 0 otherwise
static int is_white_piece(char c) {
    return c >= 'A' && c <= 'Z';
}

// Parses a FEN string and sets up the board position
// Used to load arbitrary chess positions
static void pos_from_fen(Pos *p, const char *fen) {
    memset(p->b, '.', 64);
    p->white_to_move = 1;

    char buf[256];
    strncpy(buf, fen, sizeof(buf) - 1);
    buf[sizeof(buf) - 1] = 0;

    char *pl = strtok(buf, " ");
    char *stm = strtok(NULL, " ");
    char *cas = strtok(NULL, " ");

    if (stm) {
        p->white_to_move = (strcmp(stm, "w") == 0);
    }

    p->castle_wk = p->castle_wq = p->castle_bk = p->castle_bq = 0;

    if (cas && strcmp(cas, "-") != 0) {
        for (int i = 0; cas[i]; i++) {
            switch (cas[i]) {
                case 'K':
                    p->castle_wk = 1;
                    break;
                case 'Q':
                    p->castle_wq = 1;
                    break;
                case 'k':
                    p->castle_bk = 1;
                    break;
                case 'q':
                    p->castle_bq = 1;
                    break;
            }
        }
    }

    int rank = 7;
    int file = 0;

    for (size_t i = 0; pl && pl[i]; i++) {
        char c = pl[i];

        if (c == '/') {
            rank--;
            file = 0;
            continue;
        }

        if (isdigit((unsigned char)c)) {
            file += c - '0';
            continue;
        }

        int idx = rank * 8 + file;
        if (idx >= 0 && idx < 64) {
            p->b[idx] = c;
        }
        file++;
    }
}

// Sets the board to the standard starting chess position
static void pos_start(Pos *p) {
    pos_from_fen(p, "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1");
}

// Checks if a square is attacked by a given side
// Used for check detection and move legality
static int is_square_attacked(const Pos *p, int sq, int by_white) {
    int r = sq / 8;
    int f = sq % 8;

    if (by_white) {
        if (r > 0 && f > 0 && p->b[(r - 1) * 8 + (f - 1)] == 'P') {
            return 1;
        }
        if (r > 0 && f < 7 && p->b[(r - 1) * 8 + (f + 1)] == 'P') {
            return 1;
        }
    } else {
        if (r < 7 && f > 0 && p->b[(r + 1) * 8 + (f - 1)] == 'p') {
            return 1;
        }
        if (r < 7 && f < 7 && p->b[(r + 1) * 8 + (f + 1)] == 'p') {
            return 1;
        }
    }

    static const int nd[8] = { -17, -15, -10, -6, 6, 10, 15, 17 };

    for (int i = 0; i < 8; i++) {
        int to = sq + nd[i];
        if (to < 0 || to >= 64) {
            continue;
        }

        int tr = to / 8;
        int tf = to % 8;
        int dr = tr - r;
        int df = tf - f;

        if (dr < 0) {
            dr = -dr;
        }
        if (df < 0) {
            df = -df;
        }

        if (!((dr == 1 && df == 2) || (dr == 2 && df == 1))) {
            continue;
        }

        char pc = p->b[to];
        if (by_white && pc == 'N') {
            return 1;
        }
        if (!by_white && pc == 'n') {
            return 1;
        }
    }

    static const int dirs[8][2] = {
        { 1, 0 }, { -1, 0 }, { 0, 1 }, { 0, -1 },
        { 1, 1 }, { 1, -1 }, { -1, 1 }, { -1, -1 }
    };

    for (int di = 0; di < 8; di++) {
        int df2 = dirs[di][0];
        int dr2 = dirs[di][1];
        int cr = r + dr2;
        int cf = f + df2;

        while (cr >= 0 && cr < 8 && cf >= 0 && cf < 8) {
            int idx = cr * 8 + cf;
            char pc = p->b[idx];

            if (pc != '.') {
                if (is_white_piece(pc) == by_white) {
                    char up = (char)toupper((unsigned char)pc);

                    if (up == 'Q') {
                        return 1;
                    }
                    if (di < 4 && up == 'R') {
                        return 1;
                    }
                    if (di >= 4 && up == 'B') {
                        return 1;
                    }
                    if (up == 'K' && abs(cr - r) <= 1 && abs(cf - f) <= 1) {
                        return 1;
                    }
                }
                break;
            }

            cr += dr2;
            cf += df2;
        }
    }

    for (int rr = r - 1; rr <= r + 1; rr++) {
        for (int ff = f - 1; ff <= f + 1; ff++) {
            if (rr < 0 || rr >= 8 || ff < 0 || ff >= 8 || (rr == r && ff == f)) {
                continue;
            }

            char pc = p->b[rr * 8 + ff];
            if (by_white && pc == 'K') {
                return 1;
            }
            if (!by_white && pc == 'k') {
                return 1;
            }
        }
    }

    return 0;
}

// Determines if the current player's king is in check
static int in_check(const Pos *p, int white_king) {
    char k = white_king ? 'K' : 'k';
    int ksq = -1;

    for (int i = 0; i < 64; i++) {
        if (p->b[i] == k) {
            ksq = i;
            break;
        }
    }

    if (ksq < 0) {
        return 1;
    }

    return is_square_attacked(p, ksq, !white_king);
}

// Applies a move and returns the new position
// Handles promotions, castling, and updating state
static Pos make_move(const Pos *p, Move m) {
    Pos np = *p;
    char piece = np.b[m.from];
    np.b[m.from] = '.';

    char placed = piece;
    if (m.promo && (piece == 'P' || piece == 'p')) {
        placed = is_white_piece(piece)
            ? (char)toupper((unsigned char)m.promo)
            : (char)tolower((unsigned char)m.promo);
    }
    np.b[m.to] = placed;

    if ((piece == 'K' || piece == 'k') && abs((m.to % 8) - (m.from % 8)) == 2) {
        int ri = m.from / 8;

        if ((m.to % 8) == 6) {
            np.b[ri * 8 + 7] = '.';
            np.b[ri * 8 + 5] = (piece == 'K') ? 'R' : 'r';
        } else {
            np.b[ri * 8 + 0] = '.';
            np.b[ri * 8 + 3] = (piece == 'K') ? 'R' : 'r';
        }
    }

    if (piece == 'K') {
        np.castle_wk = 0;
        np.castle_wq = 0;
    }
    if (piece == 'k') {
        np.castle_bk = 0;
        np.castle_bq = 0;
    }
    if (m.from == 0 || m.to == 0) {
        np.castle_wq = 0;
    }
    if (m.from == 7 || m.to == 7) {
        np.castle_wk = 0;
    }
    if (m.from == 56 || m.to == 56) {
        np.castle_bq = 0;
    }
    if (m.from == 63 || m.to == 63) {
        np.castle_bk = 0;
    }

    np.white_to_move = !p->white_to_move;
    return np;
}

// Adds a move to the move list
static void add_move(Move *mv, int *n, int from, int to, char promo) {
    mv[*n].from = from;
    mv[*n].to = to;
    mv[*n].promo = promo;
    (*n)++;
}

// Generates all possible pawn moves (forward, capture, promotion)
static void gen_pawn(const Pos *p, int from, int white, Move *mv, int *n) {
    int row = from / 8;
    int col = from % 8;
    int dir = white ? 1 : -1;
    int sr = white ? 1 : 6;
    int pr = white ? 7 : 0;
    const char promos[4] = { 'q', 'r', 'b', 'n' };
    int r1 = row + dir;

    if (r1 >= 0 && r1 < 8) {
        int to = r1 * 8 + col;

        if (p->b[to] == '.') {
            if (r1 == pr) {
                for (int i = 0; i < 4; i++) {
                    add_move(mv, n, from, to, promos[i]);
                }
            } else {
                add_move(mv, n, from, to, 0);
            }

            if (row == sr && p->b[(row + 2 * dir) * 8 + col] == '.') {
                add_move(mv, n, from, (row + 2 * dir) * 8 + col, 0);
            }
        }

        int cc[2] = { col - 1, col + 1 };
        for (int i = 0; i < 2; i++) {
            if (cc[i] < 0 || cc[i] >= 8) {
                continue;
            }

            int to2 = r1 * 8 + cc[i];
            char tg = p->b[to2];

            if (tg != '.' && is_white_piece(tg) != white) {
                if (r1 == pr) {
                    for (int j = 0; j < 4; j++) {
                        add_move(mv, n, from, to2, promos[j]);
                    }
                } else {
                    add_move(mv, n, from, to2, 0);
                }
            }
        }
    }
}

// Generates all possible knight moves
static void gen_knight(const Pos *p, int from, int white, Move *mv, int *n) {
    int row = from / 8;
    int col = from % 8;

    static const int jmp[8][2] = {
        { 2, 1 }, { 2, -1 }, { -2, 1 }, { -2, -1 },
        { 1, 2 }, { 1, -2 }, { -1, 2 }, { -1, -2 }
    };

    for (int i = 0; i < 8; i++) {
        int r = row + jmp[i][0];
        int f = col + jmp[i][1];

        if (r < 0 || r >= 8 || f < 0 || f >= 8) {
            continue;
        }

        int to = r * 8 + f;
        char pc = p->b[to];

        if (pc == '.' || is_white_piece(pc) != white) {
            add_move(mv, n, from, to, 0);
        }
    }
}

// Generates moves for sliding pieces (bishop, rook, queen)
static void gen_slider(
    const Pos *p,
    int from,
    int white,
    const int dirs[][2],
    int dc,
    Move *mv,
    int *n
) {
    int row = from / 8;
    int col = from % 8;

    for (int i = 0; i < dc; i++) {
        int dr = dirs[i][0];
        int df = dirs[i][1];
        int r = row + dr;
        int f = col + df;

        while (r >= 0 && r < 8 && f >= 0 && f < 8) {
            int to = r * 8 + f;
            char pc = p->b[to];

            if (pc == '.') {
                add_move(mv, n, from, to, 0);
            } else {
                if (is_white_piece(pc) != white) {
                    add_move(mv, n, from, to, 0);
                }
                break;
            }

            r += dr;
            f += df;
        }
    }
}

// Generates king moves including castling if allowed
static void gen_king(const Pos *p, int from, int white, Move *mv, int *n) {
    int fr = from / 8;
    int ff = from % 8;

    for (int dr = -1; dr <= 1; dr++) {
        for (int df = -1; df <= 1; df++) {
            if (!dr && !df) {
                continue;
            }

            int nr = fr + dr;
            int nf = ff + df;

            if (nr < 0 || nr >= 8 || nf < 0 || nf >= 8) {
                continue;
            }

            int to = nr * 8 + nf;
            char t = p->b[to];

            if (t == '.' || is_white_piece(t) != white) {
                add_move(mv, n, from, to, 0);
            }
        }
    }

    int be = !white;

    if (white && from == 4 && !is_square_attacked(p, 4, be)) {
        /* Check king doesn't pass through or land on attacked square */
        if (p->castle_wk && p->b[5] == '.' && p->b[6] == '.' && p->b[7] == 'R' &&
            !is_square_attacked(p, 5, be) && !is_square_attacked(p, 6, be)) {
            add_move(mv, n, 4, 6, 0);
        }

        if (p->castle_wq && p->b[3] == '.' && p->b[2] == '.' && p->b[1] == '.' && p->b[0] == 'R' &&
            !is_square_attacked(p, 3, be) && !is_square_attacked(p, 2, be)) {
            add_move(mv, n, 4, 2, 0);
        }
    }

    if (!white && from == 60 && !is_square_attacked(p, 60, be)) {
        if (p->castle_bk && p->b[61] == '.' && p->b[62] == '.' && p->b[63] == 'r' &&
            !is_square_attacked(p, 61, be) && !is_square_attacked(p, 62, be)) {
            add_move(mv, n, 60, 62, 0);
        }

        if (p->castle_bq && p->b[59] == '.' && p->b[58] == '.' && p->b[57] == '.' && p->b[56] == 'r' &&
            !is_square_attacked(p, 59, be) && !is_square_attacked(p, 58, be)) {
            add_move(mv, n, 60, 58, 0);
        }
    }
}

// Generates all moves without checking if king is left in check
// These are filtered later to get legal moves
static int pseudo_legal_moves(const Pos *p, Move *mv) {
    int n = 0;

    static const int bd[4][2] = {
        { 1, 1 }, { 1, -1 }, { -1, 1 }, { -1, -1 }
    };
    static const int rd[4][2] = {
        { 1, 0 }, { -1, 0 }, { 0, 1 }, { 0, -1 }
    };
    static const int qd[8][2] = {
        { 1, 1 }, { 1, -1 }, { -1, 1 }, { -1, -1 },
        { 1, 0 }, { -1, 0 }, { 0, 1 }, { 0, -1 }
    };

    for (int i = 0; i < 64; i++) {
        char pc = p->b[i];
        if (pc == '.') {
            continue;
        }

        int white = is_white_piece(pc);
        if (white != p->white_to_move) {
            continue;
        }

        char up = (char)toupper((unsigned char)pc);

        if (up == 'P') {
            gen_pawn(p, i, white, mv, &n);
        } else if (up == 'N') {
            gen_knight(p, i, white, mv, &n);
        } else if (up == 'B') {
            gen_slider(p, i, white, bd, 4, mv, &n);
        } else if (up == 'R') {
            gen_slider(p, i, white, rd, 4, mv, &n);
        } else if (up == 'Q') {
            gen_slider(p, i, white, qd, 8, mv, &n);
        } else if (up == 'K') {
            gen_king(p, i, white, mv, &n);
        }
    }

    return n;
}

// Filters pseudo-legal moves into fully legal moves
// Ensures king is not left in check
static int legal_moves(const Pos *p, Move *out) {
    /* King must exist */
    char k = p->white_to_move ? 'K' : 'k';
    int ksq = -1;

    for (int i = 0; i < 64; i++) {
        if (p->b[i] == k) {
            ksq = i;
            break;
        }
    }

    if (ksq < 0) {
        return 0;
    }

    Move tmp[256];
    int pn = pseudo_legal_moves(p, tmp);
    int n = 0;

    for (int i = 0; i < pn; i++) {
        /* Sanity: squares in bounds, mover is our piece */
        if (tmp[i].from < 0 || tmp[i].from > 63 || tmp[i].to < 0 || tmp[i].to > 63) {
            continue;
        }

        char mover = p->b[tmp[i].from];
        if (mover == '.' || is_white_piece(mover) != p->white_to_move) {
            continue;
        }

        /* The definitive legality test */
        Pos np = make_move(p, tmp[i]);
        if (!in_check(&np, !np.white_to_move)) {
            out[n++] = tmp[i];
        }
    }

    return n;
}

// Verifies a move is legal by checking against generated legal moves
static int move_is_legal(const Pos *p, Move m) {
    if (m.from < 0 || m.from > 63 || m.to < 0 || m.to > 63) {
        return 0;
    }
    if (m.from == m.to) {
        return 0;
    }

    char mover = p->b[m.from];
    if (mover == '.' || is_white_piece(mover) != p->white_to_move) {
        return 0;
    }

    Move legal[256];
    int n = legal_moves(p, legal);

    for (int i = 0; i < n; i++) {
        if (legal[i].from == m.from && legal[i].to == m.to && legal[i].promo == m.promo) {
            return 1;
        }
    }

    return 0;
}

// Applies a move given in UCI format (e.g., e2e4)
static void apply_uci_move(Pos *p, const char *uci) {
    if (!uci || strlen(uci) < 4) {
        return;
    }

    Move m;
    m.from = sq_index(uci);
    m.to = sq_index(uci + 2);
    m.promo = (strlen(uci) >= 5) ? uci[4] : 0;

    *p = make_move(p, m);
}

// Parses a UCI "position" command and updates the board
static void parse_position(Pos *p, const char *line) {
    char buf[1024];
    strncpy(buf, line, sizeof(buf) - 1);
    buf[sizeof(buf) - 1] = 0;

    char *toks[128];
    int nt = 0;

    for (char *tok = strtok(buf, " \t\r\n"); tok && nt < 128; tok = strtok(NULL, " \t\r\n")) {
        toks[nt++] = tok;
    }

    int i = 1;

    if (i < nt && strcmp(toks[i], "startpos") == 0) {
        pos_start(p);
        i++;
    } else if (i < nt && strcmp(toks[i], "fen") == 0) {
        i++;
        char fen[512] = { 0 };

        for (int k = 0; k < 6 && i < nt; k++, i++) {
            if (k) {
                strcat(fen, " ");
            }
            strcat(fen, toks[i]);
        }

        pos_from_fen(p, fen);
    }

    game_history_len = 0;
    game_history[game_history_len++] = compute_hash(p);

    if (i < nt && strcmp(toks[i], "moves") == 0) {
        i++;
        for (; i < nt; i++) {
            apply_uci_move(p, toks[i]);
            if (game_history_len < MAX_HISTORY) {
                game_history[game_history_len++] = compute_hash(p);
            }
        }
    }
}

// Outputs the best move in UCI format
static void print_bestmove(Move m) {
    char a[3], b[3];
    index_to_sq(m.from, a);
    index_to_sq(m.to, b);

    if (m.promo) {
        printf("bestmove %s%s%c\n", a, b, m.promo);
    } else {
        printf("bestmove %s%s\n", a, b);
    }
    fflush(stdout);
}

static const int MATERIAL[7] = { 0, 100, 320, 330, 500, 900, 20000 };

// Returns a numeric type for a piece (used for evaluation)
static int piece_type(char c) {
    switch ((char)toupper((unsigned char)c)) {
        case 'P': return 1;
        case 'N': return 2;
        case 'B': return 3;
        case 'R': return 4;
        case 'Q': return 5;
        case 'K': return 6;
    }
    return 0;
}

static const int PST_PAWN[64] = {
     0,  0,  0,  0,  0,  0,  0,  0,
    50, 50, 50, 50, 50, 50, 50, 50,
    10, 10, 20, 30, 30, 20, 10, 10,
     5,  5, 10, 25, 25, 10,  5,  5,
     0,  0,  0, 20, 20,  0,  0,  0,
     5, -5, -10,  0,  0, -10, -5,  5,
     5, 10, 10, -20, -20, 10, 10,  5,
     0,  0,  0,  0,  0,  0,  0,  0
};

static const int PST_KNIGHT[64] = {
    -50, -40, -30, -30, -30, -30, -40, -50,
    -40, -20,   0,   0,   0,   0, -20, -40,
    -30,   0,  10,  15,  15,  10,   0, -30,
    -30,   5,  15,  20,  20,  15,   5, -30,
    -30,   0,  15,  20,  20,  15,   0, -30,
    -30,   5,  10,  15,  15,  10,   5, -30,
    -40, -20,   0,   5,   5,   0, -20, -40,
    -50, -40, -30, -30, -30, -30, -40, -50
};

static const int PST_BISHOP[64] = {
    -20, -10, -10, -10, -10, -10, -10, -20,
    -10,   0,   0,   0,   0,   0,   0, -10,
    -10,   0,   5,  10,  10,   5,   0, -10,
    -10,   5,   5,  10,  10,   5,   5, -10,
    -10,   0,  10,  10,  10,  10,   0, -10,
    -10,  10,  10,  10,  10,  10,  10, -10,
    -10,   5,   0,   0,   0,   0,   5, -10,
    -20, -10, -10, -10, -10, -10, -10, -20
};

static const int PST_ROOK[64] = {
     0,  0,  0,  0,  0,  0,  0,  0,
     5, 10, 10, 10, 10, 10, 10,  5,
    -5,  0,  0,  0,  0,  0,  0, -5,
    -5,  0,  0,  0,  0,  0,  0, -5,
    -5,  0,  0,  0,  0,  0,  0, -5,
    -5,  0,  0,  0,  0,  0,  0, -5,
    -5,  0,  0,  0,  0,  0,  0, -5,
     0,  0,  0,  5,  5,  0,  0,  0
};

static const int PST_QUEEN[64] = {
    -20, -10, -10, -5, -5, -10, -10, -20,
    -10,   0,   0,  0,  0,   0,   0, -10,
    -10,   0,   5,  5,  5,   5,   0, -10,
     -5,   0,   5,  5,  5,   5,   0,  -5,
      0,   0,   5,  5,  5,   5,   0,  -5,
    -10,   5,   5,  5,  5,   5,   0, -10,
    -10,   0,   5,  0,  0,   0,   0, -10,
    -20, -10, -10, -5, -5, -10, -10, -20
};

static const int PST_KING[64] = {
    -30, -40, -40, -50, -50, -40, -40, -30,
    -30, -40, -40, -50, -50, -40, -40, -30,
    -30, -40, -40, -50, -50, -40, -40, -30,
    -30, -40, -40, -50, -50, -40, -40, -30,
    -20, -30, -30, -40, -40, -30, -30, -20,
    -10, -20, -20, -20, -20, -20, -20, -10,
     20,  20,   0,   0,   0,   0,  20,  20,
     20,  30,  10,   0,   0,  10,  30,  20
};

// Returns positional score from piece-square tables
static int pst_score(char pc, int sq) {
    int rank = sq / 8;
    int file = sq % 8;
    int white = is_white_piece(pc);
    int pst_sq = white ? sq : (7 - rank) * 8 + file;

    switch ((char)toupper((unsigned char)pc)) {
        case 'P': return PST_PAWN[pst_sq];
        case 'N': return PST_KNIGHT[pst_sq];
        case 'B': return PST_BISHOP[pst_sq];
        case 'R': return PST_ROOK[pst_sq];
        case 'Q': return PST_QUEEN[pst_sq];
        case 'K': return PST_KING[pst_sq];
    }

    return 0;
}

// Evaluates the board position (material + positional value)
static int evaluate(const Pos *p) {
    int score = 0;

    for (int i = 0; i < 64; i++) {
        char pc = p->b[i];
        if (pc == '.') {
            continue;
        }

        int val = MATERIAL[piece_type(pc)] + pst_score(pc, i);
        if (is_white_piece(pc)) {
            score += val;
        } else {
            score -= val;
        }
    }

    return p->white_to_move ? score : -score;
}

// Scores moves for move ordering (captures prioritized)
static int move_score_ord(const Pos *p, Move m) {
    char v = p->b[m.to];
    char a = p->b[m.from];

    if (v == '.') {
        return 0;
    }

    return 10 * MATERIAL[piece_type(v)] - MATERIAL[piece_type(a)] + 10000;
}

// Sorts moves to improve search efficiency
static void sort_moves(const Pos *p, Move *mv, int n) {
    for (int i = 1; i < n; i++) {
        Move key = mv[i];
        int ks = move_score_ord(p, key);
        int j = i - 1;

        while (j >= 0 && move_score_ord(p, mv[j]) < ks) {
            mv[j + 1] = mv[j];
            j--;
        }
        mv[j + 1] = key;
    }
}

#define INF 1000000
#define MAX_DEPTH 6
#define TIME_LIMIT_MS 9000
#define REPETITION_PENALTY 150

static double g_deadline = 0.0;
static int g_timeout = 0;

// Returns current time in seconds (used for time control)
static double now_sec(void) {
    return (double)clock() / CLOCKS_PER_SEC;
}

// Extends search on capture moves to avoid horizon effect
static int quiescence(const Pos *p, int alpha, int beta) {
    int sp = evaluate(p);
    if (sp >= beta) {
        return beta;
    }
    if (sp > alpha) {
        alpha = sp;
    }

    Move mv[256];
    int n = legal_moves(p, mv);
    sort_moves(p, mv, n);

    for (int i = 0; i < n; i++) {
        if (p->b[mv[i].to] == '.') {
            continue;
        }

        Pos np = make_move(p, mv[i]);
        int score = -quiescence(&np, -beta, -alpha);

        if (score >= beta) {
            return beta;
        }
        if (score > alpha) {
            alpha = score;
        }
    }

    return alpha;
}

// Core recursive search using negamax with alpha-beta pruning
static int negamax(
    const Pos *p,
    int depth,
    int alpha,
    int beta,
    unsigned long long *ss,
    int sl
) {
    if (now_sec() >= g_deadline) {
        g_timeout = 1;
        return evaluate(p);
    }

    unsigned long long h = compute_hash(p);
    if (sl > 0 && count_reps(h, ss, sl) >= 1) {
        return 0;
    }

    if (depth == 0) {
        return quiescence(p, alpha, beta);
    }

    Move mv[256];
    int n = legal_moves(p, mv);

    if (n == 0) {
        return in_check(p, p->white_to_move) ? -INF + (MAX_DEPTH - depth) : 0;
    }

    sort_moves(p, mv, n);

    if (sl < MAX_HISTORY) {
        ss[sl] = h;
    }

    for (int i = 0; i < n; i++) {
        Pos np = make_move(p, mv[i]);
        int score = -negamax(&np, depth - 1, -beta, -alpha, ss, sl + 1);

        if (g_timeout) {
            return alpha;
        }
        if (score >= beta) {
            return beta;
        }
        if (score > alpha) {
            alpha = score;
        }
    }

    return alpha;
}

// Searches and returns the best move from current position
static Move find_best_move(const Pos *p) {
    Move mv[256];
    int n = legal_moves(p, mv);

    if (n == 0) {
        Move null = { -1, -1, 0 };
        return null;
    }

    sort_moves(p, mv, n);
    g_timeout = 0;
    g_deadline = now_sec() + (TIME_LIMIT_MS / 1000.0);

    Move best = mv[0];
    int best_score = -INF - 1;
    unsigned long long ss[MAX_HISTORY];
    ss[0] = compute_hash(p);

    for (int i = 0; i < n; i++) {
        if (g_timeout) {
            break;
        }

        Pos np = make_move(p, mv[i]);
        unsigned long long ch = compute_hash(&np);
        int score = -negamax(&np, MAX_DEPTH - 1, -INF, INF, ss, 1);
        int reps = count_reps(ch, NULL, 0);

        if (reps >= 2) {
            score -= REPETITION_PENALTY * 3;
        } else if (reps >= 1) {
            score -= REPETITION_PENALTY;
        }

        if (score > best_score) {
            best_score = score;
            best = mv[i];
        }
    }

    return best;
}

// Main loop handling UCI commands and engine interaction
int main(void) {
    zobrist_init();

    Pos pos;
    pos_start(&pos);

    game_history_len = 0;
    game_history[game_history_len++] = compute_hash(&pos);

    char line[1024];

    while (fgets(line, sizeof(line), stdin)) {
        size_t len = strlen(line);

        while (len && (line[len - 1] == '\n' || line[len - 1] == '\r')) {
            line[--len] = 0;
        }

        if (!len) {
            continue;
        }

        if (strcmp(line, "uci") == 0) {
            printf("id name team_c\n");
            printf("id author team_c_bryan\n");
            printf("uciok\n");
            fflush(stdout);
        } else if (strcmp(line, "isready") == 0) {
            printf("readyok\n");
            fflush(stdout);
        } else if (strcmp(line, "ucinewgame") == 0) {
            pos_start(&pos);
            game_history_len = 0;
            game_history[game_history_len++] = compute_hash(&pos);
        } else if (strncmp(line, "position", 8) == 0) {
            parse_position(&pos, line);
        } else if (strncmp(line, "go", 2) == 0) {
            Move best = find_best_move(&pos);

            /*
             * FINAL SAFETY GATE: before transmitting any move, verify it is
             * legal in the current position. If something went wrong anywhere
             * in the search (timeout, edge case), this catches it and falls
             * back to the first legal move so we never output an illegal move.
             */
            if (best.from < 0 || !move_is_legal(&pos, best)) {
                Move fb[256];
                int fn = legal_moves(&pos, fb);

                if (fn > 0) {
                    print_bestmove(fb[0]);
                } else {
                    printf("bestmove 0000\n");
                    fflush(stdout);
                }
            } else {
                print_bestmove(best);
            }
        } else if (strcmp(line, "quit") == 0) {
            break;
        }
    }

    return 0;
}
