/* Cycle packing with ruin-and-recreate in Q_n (n<=9).
   sides=1: S = union of pairwise nonadjacent induced cycles in Q_n (use n=9 for direct Q9).
   sides=2: A,B each such a union in Q_n, A and B vertex-disjoint (fibre construction:
            n=8 -> |S|=|A|+|B| over Q1, n=7 -> |S|=2(|A|+|B|) over Q2).
   All cycles have length in [G, H].
   usage: packn n sides G H seed seconds */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <stdint.h>
typedef uint64_t u64;
#define W 8
typedef struct { u64 w[W]; } bs;
static int n, NV, G, H, sides;
static bs NB[512];
static inline int bget(const bs *m,int i){ return (m->w[i>>6]>>(i&63))&1; }
static inline void bset(bs *m,int i){ m->w[i>>6]|=1ULL<<(i&63); }
static inline void bor(bs *a,const bs *b){ for(int i=0;i<W;i++) a->w[i]|=b->w[i]; }
static inline int bpc(const bs *a){ int c=0; for(int i=0;i<W;i++) c+=__builtin_popcountll(a->w[i]); return c; }
static u64 rs=88172645463325252ULL;
static unsigned rnd(unsigned k){ rs^=rs<<13; rs^=rs>>7; rs^=rs<<17; return (unsigned)(rs%k); }
static int path[512], found[512], found_len; static long long steps, steplim;
static int dfs(int len, bs *ban, const bs *forb, int s){
    if(++steps>steplim) return 0;
    int h=path[len-1]; int order[9]; for(int k=0;k<n;k++) order[k]=k;
    for(int k=n-1;k>0;k--){int j=rnd(k+1);int t=order[k];order[k]=order[j];order[j]=t;}
    for(int q=0;q<n;q++){
        int y=h^(1<<order[q]);
        if(bget(ban,y)||bget(forb,y)) continue;
        if(bget(&NB[s],y)){
            if(len+1>=G && len+1<=H){ path[len]=y; found_len=len+1; memcpy(found,path,sizeof(int)*(len+1)); return 1; }
            continue;
        }
        if(len+1>=H) continue;
        path[len]=y;
        bs nb=*ban; bor(&nb,&NB[h]); bset(&nb,h);
        if(dfs(len+1,&nb,forb,s)) return 1;
    }
    return 0;
}
static int find_cycle(const bs *forb, int *out, long long lim, int nstart){
    int starts[512], ns=0; for(int v=0;v<NV;v++) if(!bget(forb,v)) starts[ns++]=v;
    for(int k=ns-1;k>0;k--){int j=rnd(k+1);int t=starts[k];starts[k]=starts[j];starts[j]=t;}
    for(int i=0;i<ns&&i<nstart;i++){
        int s=starts[i]; int x=s^(1<<rnd(n)); if(bget(forb,x)) continue;
        path[0]=s; path[1]=x; steps=0; steplim=lim;
        bs ban; memset(&ban,0,sizeof ban); bset(&ban,s); bset(&ban,x);
        if(dfs(2,&ban,forb,s)){ memcpy(out,found,sizeof(int)*found_len); return found_len; }
    }
    return 0;
}
#define MAXC 64
typedef struct { int nc[2]; int len[2][MAXC]; int cyc[2][MAXC][512]; } state;
static void masks(const state *st, bs *S, bs *CL){
    for(int s=0;s<2;s++){ memset(&S[s],0,sizeof(bs)); memset(&CL[s],0,sizeof(bs));
        for(int c=0;c<st->nc[s];c++) for(int i=0;i<st->len[s][c];i++){ int v=st->cyc[s][c][i]; bset(&S[s],v); bset(&CL[s],v); bor(&CL[s],&NB[v]); } }
}
static int total(const state *st){ int t=0; for(int s=0;s<sides;s++) for(int c=0;c<st->nc[s];c++) t+=st->len[s][c]; return t; }
static int verify_cycle(const int *c,int L){ /* induced cycle check */
    bs m; memset(&m,0,sizeof m); for(int i=0;i<L;i++){ if(bget(&m,c[i])) return 0; bset(&m,c[i]); }
    for(int i=0;i<L;i++){ int d=0; for(int k=0;k<n;k++) d+=bget(&m,c[i]^(1<<k)); if(d!=2) return 0; }
    return 1;
}
static void fill(state *st, int tries, long long lim){
    for(int t=0;t<tries;t++){
        int s=rnd(sides); if(st->nc[s]>=MAXC) continue;
        bs S[2],CL[2]; masks(st,S,CL);
        bs forb=CL[s]; if(sides==2) bor(&forb,&S[1-s]);
        int c[512]; int L=find_cycle(&forb,c,lim,6);
        if(L && verify_cycle(c,L)){ int k=st->nc[s]++; st->len[s][k]=L; memcpy(st->cyc[s][k],c,sizeof(int)*L); }
    }
}
static void ruin(state *st, int k){
    for(int r=0;r<k;r++){ int s=rnd(sides); if(!st->nc[s]) continue; int c=rnd(st->nc[s]);
        int last=--st->nc[s]; if(c!=last){ st->len[s][c]=st->len[s][last]; memcpy(st->cyc[s][c],st->cyc[s][last],sizeof(int)*512);} }
}
static void dump(const state *st, const char *tag){
    printf("{\"tag\":\"%s\",\"n\":%d,\"sides\":%d,\"G\":%d,\"total\":%d",tag,n,sides,G,total(st));
    for(int s=0;s<sides;s++){ printf(",\"%c\":[",'A'+s);
        for(int c=0;c<st->nc[s];c++){ printf("%s[",c?",":""); for(int i=0;i<st->len[s][c];i++) printf("%s%d",i?",":"",st->cyc[s][c][i]); printf("]"); }
        printf("]"); }
    printf("}\n"); fflush(stdout);
}
int main(int argc,char**argv){
    n=atoi(argv[1]); sides=atoi(argv[2]); G=atoi(argv[3]); H=atoi(argv[4]);
    rs^=(u64)atoll(argv[5])*0x9E3779B97F4A7C15ULL; for(int i=0;i<20;i++) rnd(2);
    int secs=atoi(argv[6]); long long lim=argc>7?atoll(argv[7]):100000;
    NV=1<<n; for(int v=0;v<NV;v++){ memset(&NB[v],0,sizeof(bs)); for(int k=0;k<n;k++) bset(&NB[v],v^(1<<k)); }
    static state cur, cand, best; memset(&cur,0,sizeof cur);
    fill(&cur,40,lim); best=cur; int bt=total(&best); dump(&best,"init");
    time_t t0=time(0); long long it=0;
    while(time(0)-t0<secs){
        it++; cand=cur; ruin(&cand,1+rnd(2)); fill(&cand,12,lim);
        int tc=total(&cand), tu=total(&cur);
        if(tc>=tu || rnd(100)<2) cur=cand;
        if(total(&cur)>bt){ best=cur; bt=total(&best); dump(&best,"best"); }
    }
    fprintf(stderr,"iters %lld best %d\n",it,bt);
    return 0;
}
