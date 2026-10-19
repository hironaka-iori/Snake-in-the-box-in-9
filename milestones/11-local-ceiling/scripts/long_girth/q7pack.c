/* Fibre construction over Q7 x Q2: find disjoint A,B in Q7, each a union of pairwise
   nonadjacent induced cycles of length >= G, maximizing |A|+|B|. Randomized DFS.
   B is one induced cycle (length LB); A = cycles packed in Q7 \ B (only vertex-disjointness
   from B is needed; A's cycles must be mutually nonadjacent).
   usage: q7pack seed seconds G */
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
typedef unsigned __int128 u128;
#define NV 128
#define ND 7
static u128 NB[NV], CN[NV];
static int path[NV];
static u128 forbid_g; static int tmin, tmax; static long long steps, steplim;
static int found_len, found[NV];
static unsigned long long rs=88172645463325252ULL;
static unsigned rnd(unsigned n){ rs^=rs<<13; rs^=rs>>7; rs^=rs<<17; return (unsigned)(rs%n); }
static int bit(u128 m,int i){ return (int)((m>>i)&1); }
static int dfs(int len, u128 ban, int s){
    if(++steps>steplim) return 0;
    int h=path[len-1]; int order[ND]; for(int k=0;k<ND;k++) order[k]=k;
    for(int k=ND-1;k>0;k--){int j=rnd(k+1);int t=order[k];order[k]=order[j];order[j]=t;}
    for(int q=0;q<ND;q++){
        int y=h^(1<<order[q]);
        if(bit(ban,y)||bit(forbid_g,y)) continue;
        if(bit(NB[s],y)){
            /* closing vertex y adjacent to s: y must not be adjacent to other path vertices (ban covers
               path[0..len-2] closed nbhds except s's); since y in NB[s], y not banned by s means s's CN not in ban */
            if(len+1>=tmin && len+1<=tmax){ path[len]=y; found_len=len+1; for(int i=0;i<=len;i++) found[i]=path[i]; return 1; }
            continue;
        }
        if(len+1>=tmax) continue;
        path[len]=y;
        if(dfs(len+1, ban|CN[h], s)) return 1;
    }
    return 0;
}
/* find induced cycle in allowed region (not forbid), length in [lo,hi]; returns len */
static int find_cycle(u128 forbid, int lo, int hi, int *out, long long lim){
    forbid_g=forbid; tmin=lo; tmax=hi; steplim=lim;
    int starts[NV]; int ns=0; for(int v=0;v<NV;v++) if(!bit(forbid,v)) starts[ns++]=v;
    for(int k=ns-1;k>0;k--){int j=rnd(k+1);int t=starts[k];starts[k]=starts[j];starts[j]=t;}
    for(int i=0;i<ns && i<8;i++){
        int s=starts[i]; int a=rnd(ND); int x=s^(1<<a); if(bit(forbid,x)) continue;
        path[0]=s; path[1]=x; steps=0;
        /* ban: s itself and x; s's other nbrs are banned once we leave x (CN[x] added at next step);
           closure handled by NB[s] test. path vertices besides s must not be adjacent to s except
           path[1] and the last: enforce by banning NB[s] except x at depth>=2 */
        u128 ban=((u128)1<<s)|((u128)1<<x);
        if(dfs(2, ban, s)){ for(int j=0;j<found_len;j++) out[j]=found[j]; return found_len; }
    }
    return 0;
}
static int verify(int *c,int L,u128 *mask){
    u128 m=0; for(int i=0;i<L;i++){ if(bit(m,c[i])) return 0; m|=(u128)1<<c[i]; }
    for(int i=0;i<L;i++){ u128 t=NB[c[i]]&m; int d=__builtin_popcountll((unsigned long long)t)+__builtin_popcountll((unsigned long long)(t>>64)); if(d!=2) return 0; }
    *mask=m; return 1;
}
static u128 closed(u128 m){ u128 r=m; for(int v=0;v<NV;v++) if(bit(m,v)) r|=NB[v]; return r; }
static int pc(u128 m){ return __builtin_popcountll((unsigned long long)m)+__builtin_popcountll((unsigned long long)(m>>64)); }
static void pr(u128 m){ int f=1; for(int v=0;v<NV;v++) if(bit(m,v)){ printf("%s%d",f?"":",",v); f=0; } }
int main(int argc,char**argv){
    rs ^= (unsigned long long)(argc>1?atoi(argv[1]):1)*2654435761ULL; for(int i=0;i<10;i++) rnd(2);
    int secs=argc>2?atoi(argv[2]):60, G=argc>3?atoi(argv[3]):28;
    for(int v=0;v<NV;v++){NB[v]=0;for(int k=0;k<ND;k++)NB[v]|=(u128)1<<(v^(1<<k));CN[v]=NB[v]|((u128)1<<v);}
    int best=0; time_t t0=time(0); long long it=0;
    while(time(0)-t0<secs){
        it++;
        /* B: one or more cycles. A: cycles in complement of B. Both built greedily. */
        u128 S[2]={0,0}; int len[2][8]; int nc[2]={0,0};
        for(int side=0; side<2; side++){
            for(int tries=0; tries<6; tries++){
                u128 forb = closed(S[side]) | S[1-side];
                int lo = G, hi = 48; /* random target window */
                int want = G + rnd(48-G+1); lo = want;
                int c[NV]; int L=find_cycle(forb, lo, hi, c, 200000);
                u128 m; if(!L || !verify(c,L,&m)) continue;
                /* the cycle must be induced and nonadjacent to the rest of S[side] (forb ensures) */
                S[side]|=m; len[side][nc[side]++]=L;
            }
        }
        int tot=pc(S[0])+pc(S[1]);
        if(tot>best){ best=tot;
            printf("{\"G\":%d,\"total\":%d,\"lensA\":[",G,tot); for(int i=0;i<nc[0];i++)printf("%s%d",i?",":"",len[0][i]);
            printf("],\"lensB\":["); for(int i=0;i<nc[1];i++)printf("%s%d",i?",":"",len[1][i]);
            printf("],\"A\":["); pr(S[0]); printf("],\"B\":["); pr(S[1]); printf("],\"iter\":%lld}\n",it); fflush(stdout); }
    }
    fprintf(stderr,"iters %lld best %d\n",it,best);
    return 0;
}
