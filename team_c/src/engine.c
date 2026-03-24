#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>

// Minimal UCI engine: first legal move.
// No castling, no en-passant; promotions -> queen only.

typedef struct {
    int from, to; // 0-63 square indices
    char promo; // promotion piece, or 0 if not a promotion
} Move;

typedef struct {
    char b[64];
    int white_to_move;
    //ADDED FOR CASTLING
    int castle_wk; //castle white kingside
    int castle_wq; //castle white queenside
    int castle_bk; //castle black kingside
    int castle_bq; //castle black queenside
} Pos;

static int sq_index(const char *s) {
    int file = s[0] - 'a'; // gives 0-7 for a-h (column)
    int rank = s[1] - '1'; // gives 0-7 for 1-8 (row)
    return rank * 8 + file; 
}

static void index_to_sq(int idx, char out[3]) {
    out[0] = (char) ('a' + (idx % 8)); // gives letter a-h (column)
    out[1] = (char) ('1' + (idx / 8)); // gives number 1-8 (row)
    out[2] = 0; // null terminator for string
}

static void pos_from_fen(Pos *p, const char *fen) {
    memset(p->b, '.', 64); // fills up the chess board with "." to represent empty squares
    p->white_to_move = 1; // white moves first by default

    char buf[256];
    strncpy(buf, fen, sizeof(buf)-1); // copy fen to buf, ensuring null-termination
    buf[sizeof(buf) - 1] = 0;

    char *save = NULL;
    char *placement = strtok_r(buf, " ", &save); // first token is piece placement
    char *stm = strtok_r(NULL, " ", &save); // second token is side to move
    char *castle_str = strtok_r(NULL, " ", &save); //ADDED FOR CASTLING
    
    if (stm) p->white_to_move = (strcmp(stm, "w") == 0); // if stm is "w", white_to_move is 1, else 0
    
    //ADDED FOR CASTLING
    p->castle_wk = p->castle_wq = p->castle_bk = p->castle_bq = 0;
    if (castle_str && strcmp(castle_str, "-") != 0) {
        for (int i = 0; castle_str[i]; i++) {
            switch (castle_str[i]) {
                case 'K': p->castle_wk = 1; break;
                case 'Q': p->castle_wq = 1; break;
                case 'k': p->castle_bk = 1; break;
                case 'q': p->castle_bq = 1; break;
            }
        }
    }
    

    int rank = 7, file = 0;
    for (size_t i = 0; placement && placement[i]; i++) {
        char c = placement[i];
        if (c == '/') {
            rank--;
            file = 0;
            continue;
        }
        if (isdigit((unsigned char) c)) {
            file += c - '0';
            continue;
        }
        int idx = rank * 8 + file;
        if (idx >= 0 && idx < 64) p->b[idx] = c;
        file++;
    }
}

static void pos_start(Pos *p) {
    pos_from_fen(p, "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w - - 0 1"); // lowercase = black, uppercase = white
}

static int is_white_piece(char c) { return c >= 'A' && c <= 'Z'; }

static int is_square_attacked(const Pos *p, int sq, int by_white) {
    int r = sq / 8, f = sq % 8;

    // pawns
    if (by_white) {
        if (r > 0 && f > 0 && p->b[(r - 1) * 8 + (f - 1)] == 'P') return 1;
        if (r > 0 && f < 7 && p->b[(r - 1) * 8 + (f + 1)] == 'P') return 1;
    } else {
        if (r < 7 && f > 0 && p->b[(r + 1) * 8 + (f - 1)] == 'p') return 1;
        if (r < 7 && f < 7 && p->b[(r + 1) * 8 + (f + 1)] == 'p') return 1;
    }

    // knights
    static const int nd[8] = {-17, -15, -10, -6, 6, 10, 15, 17};
    for (int i = 0; i < 8; i++) {
        int to = sq + nd[i];
        if (to < 0 || to >= 64) continue;
        int tr = to / 8, tf = to % 8;
        int dr = tr - r;
        if (dr < 0) dr = -dr;
        int df = tf - f;
        if (df < 0) df = -df;
        if (!((dr == 1 && df == 2) || (dr == 2 && df == 1))) continue;
        char pc = p->b[to];
        if (by_white && pc == 'N') return 1;
        if (!by_white && pc == 'n') return 1;
    }

    // sliders
    static const int dirs[8][2] = {
        {1, 0}, {-1, 0}, {0, 1}, {0, -1},
        {1, 1}, {1, -1}, {-1, 1}, {-1, -1}
    };

    for (int di = 0; di < 8; di++) {
        int df = dirs[di][0], dr = dirs[di][1];
        int cr = r + dr, cf = f + df;
        while (cr >= 0 && cr < 8 && cf >= 0 && cf < 8) {
            int idx = cr * 8 + cf;
            char pc = p->b[idx];
            if (pc != '.') {
                int pc_white = is_white_piece(pc);
                if (pc_white == by_white) {
                    char up = (char) toupper((unsigned char) pc);
                    int rook_dir = (di < 4);
                    int bishop_dir = (di >= 4);
                    if (up == 'Q') return 1;
                    if (rook_dir && up == 'R') return 1;
                    if (bishop_dir && up == 'B') return 1;
                    if (up == 'K' && (abs(cr - r) <= 1 && abs(cf - f) <= 1)) return 1;
                }
                break;
            }
            cr += dr;
            cf += df;
        }
    }

    // king adjacency (extra safety)
    for (int rr = r - 1; rr <= r + 1; rr++) {
        for (int ff = f - 1; ff <= f + 1; ff++) {
            if (rr < 0 || rr >= 8 || ff < 0 || ff >= 8) continue;
            if (rr == r && ff == f) continue;
            char pc = p->b[rr * 8 + ff];
            if (by_white && pc == 'K') return 1;
            if (!by_white && pc == 'k') return 1;
        }
    }

    return 0;
}

// determine if the side to move's king is in check, returns 1 if true, 0 otherwise

static int in_check(const Pos *p, int white_king) {
    char k = white_king ? 'K' : 'k';
    int ksq = -1;
    for (int i = 0; i < 64; i++) if (p->b[i] == k) {
        ksq = i;
        break;
    }
    if (ksq < 0) return 1;
    return is_square_attacked(p, ksq, !white_king);
}

// make a move on the board, returning the new position. Does not check legality of the move.
static Pos make_move(const Pos *p, Move m) {
    Pos np = *p;
    char piece = np.b[m.from];
    np.b[m.from] = '.';
    char placed = piece;
    if (m.promo && (piece == 'P' || piece == 'p')) {
        placed = is_white_piece(piece)
                     ? (char) toupper((unsigned char) m.promo)
                     : (char) tolower((unsigned char) m.promo);
    }
    np.b[m.to] = placed;

    //ADDED FOR CASTLING
    if ((piece=='K' || piece=='k') && abs((m.to%8)-m.from%8))==2){
        int rank_idx = m.from / 8;
        if ((m.to%8)==6{ //kingside
            np.b[rank_idx*8+7] = '.';
            np.b[rank_idx*8+5] = (piece=='K') ? 'R' : 'r';
        }else{ //queenside
            np.b[rank_idx*8+0] = '.';
            np.b[rank_idx*8+3] = (piece=='K') ? 'R' : 'r';
        }
    }
    
    if (piece=='K') { np.castle_wk=0; np.castle_wq=0; }
    if (piece=='k') { np.castle_bk=0; np.castle_bq=0; }
    if (m.from==0  || m.to==0)  np.castle_wq=0; //a1 rook
    if (m.from==7  || m.to==7)  np.castle_wk=0; //h1 rook
    if (m.from==56 || m.to==56) np.castle_bq=0; //a8 rook
    if (m.from==63 || m.to==63) np.castle_bk=0; //h8 rook
    
    np.white_to_move = !p->white_to_move;
    return np;
}

// adds a move to the moves array and increments the move count
static void add_move(Move *moves, int *n, int from, int to, char promo) {
    moves[*n].from = from;
    moves[*n].to = to;
    moves[*n].promo = promo;
    (*n)++;
}

static void gen_pawn(const Pos *p, int from, int white, Move *moves, int *n) {

}

static void gen_knight(const Pos *p, int from, int white, Move *moves, int *n) {

}

static void gen_queen(const Pos *p, int from, int white, const int dirs[][2], int dcount, Move *moves, int *n) {

}

static void gen_bishop(const Pos *p, int from, int white, const int dirs[][2], int dcount, Move *moves, int *n) {

}

static void gen_rook(const Pos *p, int from, int white, const int dirs[][2], int dcount, Move *moves, int *n) {
    int fr = from / 8;
    int ff = from % 8;

    for (int di = 0; di < dcount; di++){
        int df = dirs[di][0];
        int dr = dirs[di][1];
        int cr = fr + dr;
        int cf = ff + df;
        while (cr>=0 && cr<8 && cf>=0 && cf<8){
            int to = cr*8+cf;
            char target = p->b[to];
            if (target == '.') {
                add_moves(moves, n, from, to, 0);
            }else if(is_white_piece(target)!=white){
                add_move(moves, n, from, to, 0); //stop after capture
                break;
            } else {
                break; //blocked by friendly piece
            }
            cr += dr;
            cf += df;
        }
    }
}

static void gen_king(const Pos *p, int from, int white, Move *moves, int *n) {
    int fr = from / 8;
    int ff = from % 8;

    for (int fr = -1; dr <= 1; dr++){
        for (int df = -1; df <= 1; df++){
            if (dr==0 && df==0) continue;
            int nr = fr + dr, nf = ff + df;
            if (nr < 0 || nr >= 8 || nf < 0 || nf >= 8) continue;
            int to = nr*8+nf;
            char target = p -> b[to];
            if (target == '.' || is_white_piece(target) != white)
                add_move(mvoes, n, from, to, 0);
        }
    }
    
    //CASTLING
    int by_enemy = !white;
    if (white){
        if (from == 4 && !is_square_attacked(p, 4, by_enemy)){
            if (p->castle_wk && p->b[5]=='.' && p->b[6]=='.' && p->b[7]=='R' //kingside castle
                && !is_square_attacked(p, 5, by_enemy))
                add_moves(moves, n, 4, 6, 0);
            if (p->castle_wq && p->b[3]=='.' && p->b[2]=='.' && p->b[1]=='.' && p->b[0]=='R' //queenside castle
                && !is_square_attacked(p, 3, by_enemy))
                add_move(moves, n, 4, 2, 0);
        }
    }else{
        if (from == 60 && !is_square_attcked(p, 60, by_enemy)){
            if (p->castle_bk && p->b[61]=='.' && p->b[62]=='.' && p->b[63]=='r' //kingside
                && !is_square_attacked(p, 61, by_enemy))
                add_move(moves, n, 60, 62, 0);  // e8->g8
            if (p->castle_bq && p->b[59]=='.' && p->b[58]=='.' && p->b[57]=='.' && p->b[56]=='r' //queenside
                && !is_square_attacked(p, 59, by_enemy))
                add_move(moves, n, 60, 58, 0);  // e8->c8
        }
    }
}

// generate all pseudo-legal moves for the side to move, returns the number of moves generated. Does not check for checks.

static int pseudo_legal_moves(const Pos *p, Move *moves) {
    int n = 0;
    int us_white = p->white_to_move;
    for (int i = 0; i < 64; i++) {
        char pc = p->b[i];
        if (pc == '.') continue;
        int white = is_white_piece(pc);
        if (white != us_white) continue;
        char up = (char) toupper((unsigned char) pc);
        if (up == 'P') gen_pawn(p, i, white, moves, &n);
        else if (up == 'N') gen_knight(p, i, white, moves, &n);
        else if (up == 'B') {
            static const int d[4][2] = {{1, 1}, {1, -1}, {-1, 1}, {-1, -1}};
            gen_bishop(p, i, white, d, 4, moves, &n);
        } else if (up == 'R') {
            static const int d[4][2] = {{1, 0}, {-1, 0}, {0, 1}, {0, -1}};
            gen_rook(p, i, white, d, 4, moves, &n);
        } else if (up == 'Q') {
            static const int d[8][2] = {{1, 1}, {1, -1}, {-1, 1}, {-1, -1}, {1, 0}, {-1, 0}, {0, 1}, {0, -1}};
            gen_queen(p, i, white, d, 8, moves, &n);
        } else if (up == 'K') gen_king(p, i, white, moves, &n);
    }
    return n;
}

// generate all legal moves for the side to move, returns the number of moves generated. Checks for checks.
static int legal_moves(const Pos *p, Move *out) {
    Move tmp[256];
    int pn = pseudo_legal_moves(p, tmp);
    int n = 0;
    for (int i = 0; i < pn; i++) {
        Pos np = make_move(p, tmp[i]);
        // after move, side who just moved is !np.white_to_move
        if (!in_check(&np, !np.white_to_move)) {
            out[n++] = tmp[i];
        }
    }
    return n;
}

static void apply_uci_move(Pos *p, const char *uci) {
    if (!uci || strlen(uci) < 4) return;
    Move m;
    m.from = sq_index(uci);
    m.to = sq_index(uci + 2);
    m.promo = (strlen(uci) >= 5) ? uci[4] : 0;
    Pos np = make_move(p, m);
    *p = np;
}

// parses UCI position command and updates the position
static void parse_position(Pos *p, const char *line) {
    // position startpos [moves ...]
    // position fen <6 fields> [moves ...]
    char buf[1024];
    strncpy(buf, line, sizeof(buf)-1);
    buf[sizeof(buf) - 1] = 0;

    char *toks[128];
    int nt = 0;
    char *save = NULL;
    for (char *tok = strtok_r(buf, " \t\r\n", &save); tok && nt < 128; tok = strtok_r(NULL, " \t\r\n", &save)) {
        toks[nt++] = tok;
    }

    int i = 1;
    if (i < nt && strcmp(toks[i], "startpos") == 0) {
        pos_start(p);
        i++;
    } else if (i < nt && strcmp(toks[i], "fen") == 0) {
        i++;
        char fen[512] = {0};
        for (int k = 0; k < 6 && i < nt; k++, i++) {
            if (k)
                strcat(fen, " ");
            strcat(fen, toks[i]);
        }
        pos_from_fen(p, fen);
    }

    // apply moves if any
    if (i < nt && strcmp(toks[i], "moves") == 0) {
        i++;
        for (; i < nt; i++) apply_uci_move(p, toks[i]);
    }
}

static void print_bestmove(Move m) {
    char a[3], b[3];
    index_to_sq(m.from, a);
    index_to_sq(m.to, b);
    if (m.promo) printf("bestmove %s%s%c\n", a, b, m.promo);
    else printf("bestmove %s%s\n", a, b);
    fflush(stdout);
}

int main(void) {
    Pos pos;
    pos_start(&pos);

    char line[1024];
    while (fgets(line, sizeof(line), stdin)) {
        // trim
        size_t len = strlen(line);
        while (len && (line[len - 1] == '\n' || line[len - 1] == '\r')) line[--len] = 0;
        if (!len) continue;

        // strcmp (input, command input compared to, how long the command input is)
        // fflush forces output immediately, without buffering
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
        } else if (strncmp(line, "position", 8) == 0) {
            parse_position(&pos, line);
        } else if (strncmp(line, "go", 2) == 0) {
            Move ms[256];
            int n = legal_moves(&pos, ms);
            if (n <= 0) {
                printf("bestmove 0000\n");
                fflush(stdout);
            } else {
                print_bestmove(ms[0]);
            }
        } else if (strcmp(line, "quit") == 0) {
            break;
        }
    }
    return 0;
}
