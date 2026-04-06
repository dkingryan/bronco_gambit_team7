#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <math.h>
#include <time.h>

typedef struct { int from, to; char promo; } Move;

typedef struct {
    char b[64];
    int  white_to_move;
    int  castle_wk, castle_wq, castle_bk, castle_bq;
} Pos;

#define MAX_NODES    80000
#define MAX_CHILDREN 220
#define UCB_C        1.41421356f
#define SIMULATIONS  800          /* playouts per move — fast enough for UCI  */
#define PLAYOUT_DEPTH 30          /* max half-moves per playout               */

typedef struct {
    Pos   pos;
    int   parent;
    Move  move_to_here;
    int   children[MAX_CHILDREN];
    int   num_children;
    int   fully_expanded;
    int   visits;
    float wins;
    Move  untried[MAX_CHILDREN];
    int   num_untried;
} MCTSNode;

static MCTSNode pool[MAX_NODES];
static int      pool_size;

static int new_node(const Pos *pos, int parent, Move m) {
    if (pool_size >= MAX_NODES) return -1;
    MCTSNode *nd = &pool[pool_size];
    memset(nd, 0, sizeof(*nd));
    nd->pos = *pos; nd->parent = parent; nd->move_to_here = m;
    return pool_size++;
}

/* ── Board helpers ────────────────────────────────────────────────────────── */

static void index_to_sq(int i, char o[3]) {
    o[0]=(char)('a'+(i%8)); o[1]=(char)('1'+(i/8)); o[2]=0;
}
static int is_white(char c) { return c>='A'&&c<='Z'; }

static void pos_from_fen(Pos *p, const char *fen) {
    memset(p->b,'.',64); p->white_to_move=1;
    char buf[256]; strncpy(buf,fen,255); buf[255]=0;
    char *pl=strtok(buf," "), *stm=strtok(NULL," "), *cas=strtok(NULL," ");
    if (stm) p->white_to_move=(strcmp(stm,"w")==0);
    p->castle_wk=p->castle_wq=p->castle_bk=p->castle_bq=0;
    if (cas&&strcmp(cas,"-")!=0)
        for(int i=0;cas[i];i++) switch(cas[i]){
            case 'K':p->castle_wk=1;break; case 'Q':p->castle_wq=1;break;
            case 'k':p->castle_bk=1;break; case 'q':p->castle_bq=1;break;
        }
    int rank=7,file=0;
    for(int i=0;pl&&pl[i];i++){
        char c=pl[i];
        if(c=='/'){rank--;file=0;continue;}
        if(isdigit((unsigned char)c)){file+=c-'0';continue;}
        int idx=rank*8+file; if(idx>=0&&idx<64) p->b[idx]=c; file++;
    }
}
static void pos_start(Pos *p){
    pos_from_fen(p,"rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1");
}

/* ── Attack / check ───────────────────────────────────────────────────────── */

static int sq_attacked(const Pos *p, int sq, int by_white) {
    int r=sq/8,f=sq%8;
    if(by_white){
        if(r>0&&f>0&&p->b[(r-1)*8+(f-1)]=='P') return 1;
        if(r>0&&f<7&&p->b[(r-1)*8+(f+1)]=='P') return 1;
    } else {
        if(r<7&&f>0&&p->b[(r+1)*8+(f-1)]=='p') return 1;
        if(r<7&&f<7&&p->b[(r+1)*8+(f+1)]=='p') return 1;
    }
    static const int nd[8]={-17,-15,-10,-6,6,10,15,17};
    for(int i=0;i<8;i++){
        int to=sq+nd[i]; if(to<0||to>=64) continue;
        int tr=to/8,tf=to%8,dr=abs(tr-r),df=abs(tf-f);
        if(!((dr==1&&df==2)||(dr==2&&df==1))) continue;
        char pc=p->b[to];
        if(by_white&&pc=='N') return 1;
        if(!by_white&&pc=='n') return 1;
    }
    static const int dirs[8][2]={{1,0},{-1,0},{0,1},{0,-1},{1,1},{1,-1},{-1,1},{-1,-1}};
    for(int di=0;di<8;di++){
        int dr=dirs[di][0],dc=dirs[di][1],cr=r+dr,cf=f+dc;
        while(cr>=0&&cr<8&&cf>=0&&cf<8){
            int idx=cr*8+cf; char pc=p->b[idx];
            if(pc!='.'){
                if(is_white(pc)==by_white){
                    char up=(char)toupper((unsigned char)pc);
                    if(up=='Q') return 1;
                    if(di<4&&up=='R') return 1;
                    if(di>=4&&up=='B') return 1;
                    if(up=='K'&&abs(cr-r)<=1&&abs(cf-f)<=1) return 1;
                }
                break;
            }
            cr+=dr; cf+=dc;
        }
    }
    for(int rr=r-1;rr<=r+1;rr++) for(int ff=f-1;ff<=f+1;ff++){
        if(rr<0||rr>=8||ff<0||ff>=8||(rr==r&&ff==f)) continue;
        char pc=p->b[rr*8+ff];
        if(by_white&&pc=='K') return 1;
        if(!by_white&&pc=='k') return 1;
    }
    return 0;
}

static int in_check(const Pos *p, int white_king) {
    char k=white_king?'K':'k'; int ksq=-1;
    for(int i=0;i<64;i++) if(p->b[i]==k){ksq=i;break;}
    if(ksq<0) return 1;
    return sq_attacked(p,ksq,!white_king);
}

/* ── Move application ─────────────────────────────────────────────────────── */

static Pos apply_move(const Pos *p, Move m) {
    Pos np=*p; char piece=np.b[m.from];
    np.b[m.from]='.';
    char placed=piece;
    if(m.promo&&(piece=='P'||piece=='p'))
        placed=is_white(piece)?(char)toupper((unsigned char)m.promo)
                              :(char)tolower((unsigned char)m.promo);
    np.b[m.to]=placed;
    if((piece=='K'||piece=='k')&&abs((m.to%8)-(m.from%8))==2){
        int ri=m.from/8;
        if((m.to%8)==6){np.b[ri*8+7]='.';np.b[ri*8+5]=(piece=='K')?'R':'r';}
        else{np.b[ri*8]='.';np.b[ri*8+3]=(piece=='K')?'R':'r';}
    }
    if(piece=='K'){np.castle_wk=0;np.castle_wq=0;}
    if(piece=='k'){np.castle_bk=0;np.castle_bq=0;}
    if(m.from==0 ||m.to==0)  np.castle_wq=0;
    if(m.from==7 ||m.to==7)  np.castle_wk=0;
    if(m.from==56||m.to==56) np.castle_bq=0;
    if(m.from==63||m.to==63) np.castle_bk=0;
    np.white_to_move=!p->white_to_move;
    return np;
}

/* ── Move generation ──────────────────────────────────────────────────────── */

static void add_move(Move *mv,int *n,int from,int to,char promo){
    mv[*n].from=from;mv[*n].to=to;mv[*n].promo=promo;(*n)++;
}

static void gen_pawn(const Pos *p,int from,int white,Move *mv,int *n){
    int row=from/8,col=from%8,dir=white?1:-1,sr=white?1:6,pr=white?7:0;
    const char promos[4]={'q','r','b','n'};
    int r1=row+dir;
    if(r1>=0&&r1<8){
        int to=r1*8+col;
        if(p->b[to]=='.'){
            if(r1==pr) for(int i=0;i<4;i++) add_move(mv,n,from,to,promos[i]);
            else add_move(mv,n,from,to,0);
            if(row==sr&&p->b[(row+2*dir)*8+col]=='.') add_move(mv,n,from,(row+2*dir)*8+col,0);
        }
        for(int d=-1;d<=1;d+=2){
            int cc=col+d; if(cc<0||cc>=8) continue;
            int to2=r1*8+cc; char tg=p->b[to2];
            if(tg!='.'&&is_white(tg)!=white){
                if(r1==pr) for(int i=0;i<4;i++) add_move(mv,n,from,to2,promos[i]);
                else add_move(mv,n,from,to2,0);
            }
        }
    }
}

static void gen_knight(const Pos *p,int from,int white,Move *mv,int *n){
    int row=from/8,col=from%8;
    static const int jmp[8][2]={{2,1},{2,-1},{-2,1},{-2,-1},{1,2},{1,-2},{-1,2},{-1,-2}};
    for(int i=0;i<8;i++){
        int r=row+jmp[i][0],f=col+jmp[i][1];
        if(r<0||r>=8||f<0||f>=8) continue;
        int to=r*8+f; char pc=p->b[to];
        if(pc=='.'||is_white(pc)!=white) add_move(mv,n,from,to,0);
    }
}

static void gen_slider(const Pos *p,int from,int white,
                       const int dirs[][2],int dc,Move *mv,int *n){
    int row=from/8,col=from%8;
    for(int i=0;i<dc;i++){
        int dr=dirs[i][0],df=dirs[i][1],r=row+dr,f=col+df;
        while(r>=0&&r<8&&f>=0&&f<8){
            int to=r*8+f; char pc=p->b[to];
            if(pc=='.') add_move(mv,n,from,to,0);
            else{ if(is_white(pc)!=white) add_move(mv,n,from,to,0); break; }
            r+=dr; f+=df;
        }
    }
}

static void gen_king(const Pos *p,int from,int white,Move *mv,int *n){
    int fr=from/8,ff=from%8;
    for(int dr=-1;dr<=1;dr++) for(int df=-1;df<=1;df++){
        if(!dr&&!df) continue;
        int nr=fr+dr,nf=ff+df;
        if(nr<0||nr>=8||nf<0||nf>=8) continue;
        int to=nr*8+nf; char t=p->b[to];
        if(t=='.'||is_white(t)!=white) add_move(mv,n,from,to,0);
    }
    int be=!white;
    if(white&&from==4&&!sq_attacked(p,4,be)){
        if(p->castle_wk&&p->b[5]=='.'&&p->b[6]=='.'&&p->b[7]=='R'&&!sq_attacked(p,5,be))
            add_move(mv,n,4,6,0);
        if(p->castle_wq&&p->b[3]=='.'&&p->b[2]=='.'&&p->b[1]=='.'&&p->b[0]=='R'&&!sq_attacked(p,3,be))
            add_move(mv,n,4,2,0);
    }
    if(!white&&from==60&&!sq_attacked(p,60,be)){
        if(p->castle_bk&&p->b[61]=='.'&&p->b[62]=='.'&&p->b[63]=='r'&&!sq_attacked(p,61,be))
            add_move(mv,n,60,62,0);
        if(p->castle_bq&&p->b[59]=='.'&&p->b[58]=='.'&&p->b[57]=='.'&&p->b[56]=='r'&&!sq_attacked(p,59,be))
            add_move(mv,n,60,58,0);
    }
}

/* Full legal moves — used only at MCTS tree nodes (not inside playouts) */
static int legal_moves(const Pos *p, Move *out) {
    static const int bd[4][2]={{1,1},{1,-1},{-1,1},{-1,-1}};
    static const int rd[4][2]={{1,0},{-1,0},{0,1},{0,-1}};
    static const int qd[8][2]={{1,1},{1,-1},{-1,1},{-1,-1},{1,0},{-1,0},{0,1},{0,-1}};
    Move tmp[256]; int pn=0;
    for(int i=0;i<64;i++){
        char pc=p->b[i]; if(pc=='.') continue;
        int w=is_white(pc); if(w!=p->white_to_move) continue;
        char up=(char)toupper((unsigned char)pc);
        if(up=='P') gen_pawn(p,i,w,tmp,&pn);
        else if(up=='N') gen_knight(p,i,w,tmp,&pn);
        else if(up=='B') gen_slider(p,i,w,bd,4,tmp,&pn);
        else if(up=='R') gen_slider(p,i,w,rd,4,tmp,&pn);
        else if(up=='Q') gen_slider(p,i,w,qd,8,tmp,&pn);
        else if(up=='K') gen_king(p,i,w,tmp,&pn);
    }
    int n=0;
    for(int i=0;i<pn;i++){
        Pos np=apply_move(p,tmp[i]);
        if(!in_check(&np,!np.white_to_move)) out[n++]=tmp[i];
    }
    return n;
}

static int fast_moves(const Pos *p, Move *out) {
    static const int bd[4][2]={{1,1},{1,-1},{-1,1},{-1,-1}};
    static const int rd[4][2]={{1,0},{-1,0},{0,1},{0,-1}};
    static const int qd[8][2]={{1,1},{1,-1},{-1,1},{-1,-1},{1,0},{-1,0},{0,1},{0,-1}};
    int n=0;
    for(int i=0;i<64;i++){
        char pc=p->b[i]; if(pc=='.') continue;
        int w=is_white(pc); if(w!=p->white_to_move) continue;
        char up=(char)toupper((unsigned char)pc);
        if(up=='P') gen_pawn(p,i,w,out,&n);
        else if(up=='N') gen_knight(p,i,w,out,&n);
        else if(up=='B') gen_slider(p,i,w,bd,4,out,&n);
        else if(up=='R') gen_slider(p,i,w,rd,4,out,&n);
        else if(up=='Q') gen_slider(p,i,w,qd,8,out,&n);
        else if(up=='K') gen_king(p,i,w,out,&n);
    }
    return n;
}

/* ── MCTS ─────────────────────────────────────────────────────────────────── */

static float ucb1(const MCTSNode *nd, int parent_visits) {
    if (nd->visits==0) return 1e30f;
    return (nd->wins/(float)nd->visits)
         + UCB_C*sqrtf(logf((float)parent_visits)/(float)nd->visits);
}

/* Phase 1 — select: walk to a leaf using UCB1 */
static int mcts_select(int idx) {
    while (pool[idx].fully_expanded && pool[idx].num_children>0) {
        float best=-1e30f; int bc=-1;
        MCTSNode *nd=&pool[idx];
        for(int i=0;i<nd->num_children;i++){
            float s=ucb1(&pool[nd->children[i]],nd->visits);
            if(s>best){best=s;bc=nd->children[i];}
        }
        if(bc<0) break;
        idx=bc;
    }
    return idx;
}

/* Phase 2 — expand: add one new child from untried moves */
static int mcts_expand(int idx) {
    MCTSNode *nd=&pool[idx];
    if(nd->num_untried==0) return idx;
    int r=rand()%nd->num_untried;
    Move m=nd->untried[r];
    nd->untried[r]=nd->untried[--nd->num_untried];
    Pos np=apply_move(&nd->pos,m);
    int child=new_node(&np,idx,m);
    if(child<0) return idx;
    nd->children[nd->num_children++]=child;
    MCTSNode *cn=&pool[child];
    cn->num_untried=legal_moves(&np,cn->untried);
    if(cn->num_untried==0) cn->fully_expanded=1;
    if(nd->num_untried==0) nd->fully_expanded=1;
    return child;
}

/*
 * Phase 3 — simulate: fast random playout using pseudo-legal moves.
 * King capture = the side that moved into check just lost.
 * Returns +1 root wins, -1 root loses, 0 draw/depth limit.
 */
static float mcts_simulate(const Pos *start, int root_white) {
    Pos cur=*start;
    Move mv[256];

    for(int depth=0;depth<PLAYOUT_DEPTH;depth++){
        int n=fast_moves(&cur,mv);
        if(n==0) break;

        /* Shuffle captures to front for a cheap capture-preference bias */
        int caps=0;
        for(int i=0;i<n;i++)
            if(cur.b[mv[i].to]!='.'){
                Move t=mv[caps];mv[caps]=mv[i];mv[i]=t;caps++;
            }

        Move chosen;
        if(caps>0&&(rand()&1)) chosen=mv[rand()%caps];
        else                   chosen=mv[rand()%n];

        /* King capture means the previous side moved into check → they lose */
        char victim=cur.b[chosen.to];
        if(victim=='K') return root_white? -1.0f : 1.0f;
        if(victim=='k') return root_white?  1.0f :-1.0f;

        cur=apply_move(&cur,chosen);
    }

    /* Depth limit reached: use material count as tiebreak */
    static const int val[256]={
        ['P']=1,['N']=3,['B']=3,['R']=5,['Q']=9,
        ['p']=-1,['n']=-3,['b']=-3,['r']=-5,['q']=-9
    };
    int score=0;
    for(int i=0;i<64;i++) score+=val[(unsigned char)cur.b[i]];
    if(score==0) return 0.0f;
    return ((score>0)==root_white) ? 0.5f : -0.5f;
}

/* Phase 4 — backpropagate: walk to root, flipping result each level */
static void mcts_backprop(int idx, float result) {
    while(idx>=0){
        pool[idx].visits++;
        pool[idx].wins+=result;
        result=-result;
        idx=pool[idx].parent;
    }
}

/* Run MCTS and return the best move found */
static Move mcts_best_move(const Pos *root_pos) {
    pool_size=0;
    Move dummy={0,0,0};
    int root=new_node(root_pos,-1,dummy);
    MCTSNode *rn=&pool[root];
    rn->num_untried=legal_moves(root_pos,rn->untried);
    if(rn->num_untried==0) return dummy;

    int root_white=root_pos->white_to_move;

    for(int sim=0;sim<SIMULATIONS;sim++){
        int leaf=mcts_select(root);
        if(pool[leaf].num_untried>0) leaf=mcts_expand(leaf);
        float result=mcts_simulate(&pool[leaf].pos,root_white);
        mcts_backprop(leaf,result);
        if(pool_size>=MAX_NODES-1) break;
    }

    /* Most-visited child = most statistically robust choice */
    int bc=-1,bv=-1;
    for(int i=0;i<rn->num_children;i++){
        int ci=rn->children[i];
        if(pool[ci].visits>bv){bv=pool[ci].visits;bc=ci;}
    }
    if(bc<0) return rn->untried[0];
    return pool[bc].move_to_here;
}

/* ── UCI plumbing ─────────────────────────────────────────────────────────── */

static void apply_uci_move(Pos *p, const char *uci) {
    if(!uci||strlen(uci)<4) return;
    Move m;
    m.from=(uci[1]-'1')*8+(uci[0]-'a');
    m.to  =(uci[3]-'1')*8+(uci[2]-'a');
    m.promo=(strlen(uci)>=5)?uci[4]:0;
    *p=apply_move(p,m);
}

static void parse_position(Pos *p, const char *line) {
    char buf[1024]; strncpy(buf,line,1023); buf[1023]=0;
    char *toks[128]; int nt=0;
    for(char *t=strtok(buf," \t\r\n");t&&nt<128;t=strtok(NULL," \t\r\n"))
        toks[nt++]=t;
    int i=1;
    if(i<nt&&strcmp(toks[i],"startpos")==0){pos_start(p);i++;}
    else if(i<nt&&strcmp(toks[i],"fen")==0){
        i++; char fen[512]={0};
        for(int k=0;k<6&&i<nt;k++,i++){if(k)strcat(fen," ");strcat(fen,toks[i]);}
        pos_from_fen(p,fen);
    }
    if(i<nt&&strcmp(toks[i],"moves")==0){i++;for(;i<nt;i++)apply_uci_move(p,toks[i]);}
}

static void print_bestmove(Move m) {
    char a[3],b[3]; index_to_sq(m.from,a); index_to_sq(m.to,b);
    if(m.promo) printf("bestmove %s%s%c\n",a,b,m.promo);
    else        printf("bestmove %s%s\n",  a,b);
    fflush(stdout);
}

int main(void) {
    srand((unsigned)time(NULL));
    Pos pos; pos_start(&pos);
    char line[1024];
    while(fgets(line,sizeof(line),stdin)){
        size_t len=strlen(line);
        while(len&&(line[len-1]=='\n'||line[len-1]=='\r')) line[--len]=0;
        if(!len) continue;
        if(strcmp(line,"uci")==0){
            printf("id name team_c_mcts\nid author team_c_bryan\nuciok\n");
            fflush(stdout);
        } else if(strcmp(line,"isready")==0){
            printf("readyok\n"); fflush(stdout);
        } else if(strcmp(line,"ucinewgame")==0){
            pos_start(&pos);
        } else if(strncmp(line,"position",8)==0){
            parse_position(&pos,line);
        } else if(strncmp(line,"go",2)==0){
            Move mv[256];
            if(legal_moves(&pos,mv)<=0){printf("bestmove 0000\n");fflush(stdout);}
            else print_bestmove(mcts_best_move(&pos));
        } else if(strcmp(line,"quit")==0){
            break;
        }
    }
    return 0;
}