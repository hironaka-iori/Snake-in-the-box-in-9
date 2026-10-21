/* Exhaustive search over the family "palette + Hamiltonian quotient":
   Q_{h+k} = Q_h x Q_k; every light cell is visited exactly once (the quotient
   walk is a Hamiltonian path of Q_k, chosen by the search); the piece in an
   even cell lies in AL[0], in an odd cell in AL[1]; transitions at TM vertices;
   every piece has >= tmin vertices (first and last >= tend).
   Maximises the number of vertices (branch and bound, exact).
   stdin: h k tmin tend AL0 AL1 TM maxnodes */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
typedef uint32_t u32;
static int h,k,tmin,tend,H,K; static u32 AL[2],TM,NB[32];
typedef struct {u32 mask; unsigned char len,end; unsigned char seq[32];} Piece;
static Piece *lib[2][32]; static int nlib[2][32],caplib[2][32];
static int par(int c){return __builtin_popcount(c)&1;}
static unsigned char cur[32];
static void addp(int p,int s,u32 mask,int len,int end){
  if(nlib[p][s]==caplib[p][s]){caplib[p][s]=caplib[p][s]?2*caplib[p][s]:256; lib[p][s]=realloc(lib[p][s],sizeof(Piece)*caplib[p][s]);}
  Piece*q=&lib[p][s][nlib[p][s]++]; q->mask=mask;q->len=len;q->end=end;memcpy(q->seq,cur,len);}
static void gen(int p,int s,int len,u32 used,u32 blocked){
  addp(p,s,used,len,cur[len-1]); int x=cur[len-1];
  for(int d=0;d<h;d++){int y=x^(1<<d); if(!((AL[p]>>y)&1)||((blocked>>y)&1)) continue;
    if(NB[y]&used&~(1u<<x)) continue; cur[len]=y; gen(p,s,len+1,used|(1u<<y),blocked|NB[x]|(1u<<y));}}
static int cmpl(const void*a,const void*b){return ((Piece*)b)->len-((Piece*)a)->len;}
static u32 *flat[2]; static unsigned char *flen[2]; static int nflat[2];
#define HS (1<<22)
static uint64_t *hk; static signed char *hv; static long filled=0;
static int longest(int p,u32 fr){
  uint64_t key=(((uint64_t)fr<<1)|p)+1; uint64_t hs=(key*0x9E3779B97F4A7C15ULL)>>42;
  while(hk[hs]){ if(hk[hs]==key) return hv[hs]; hs=(hs+1)&(HS-1);}
  int r=0; for(int t=0;t<nflat[p];t++) if(!(flat[p][t]&~fr)){r=flen[p][t];break;}
  if(filled<HS/2){hk[hs]=key;hv[hs]=r;filled++;} return r;}
static u32 occ[64]; static int vis[64], order[64];
static Piece* ch[64];
static long long nodes=0,maxnodes=0; static int best=0;
static u32 closedm(u32 s){u32 r=s; for(int x=0;x<H;x++) if((s>>x)&1) r|=NB[x]; return r;}
static int ub(int cc,int e){ int t=0; for(int c=0;c<K;c++) if(!vis[c]){ u32 fr=AL[par(c)]; for(int j=0;j<k;j++){int c3=c^(1<<j); fr&=~(c3==cc? (occ[c3]&~(1u<<e)) : occ[c3]);} t+=longest(par(c),fr);} return t;}
static void dump(int n,int total){
  printf("BEST %d :",total); for(int i=0;i<n;i++){printf(" [c%d:",order[i]); for(int z=0;z<ch[i]->len;z++) printf("%s%d",z?",":"",ch[i]->seq[z]); printf("]");} printf("\n"); fflush(stdout);}
static void dfs(int i,int c,int s,int total){
  if(maxnodes&&nodes>maxnodes) return; nodes++;
  int p=par(c); order[i]=c; vis[c]=1;
  int prev = i? order[i-1] : -1;
  u32 bad=0; for(int j=0;j<k;j++){int c2=c^(1<<j); if(c2!=prev) bad|=occ[c2];}
  u32 pv= i? occ[prev]&~(1u<<s):0;
  int last=(i==K-1);
  int xs[32],nx=0; if(i==0){for(int x=0;x<H;x++) if((AL[p]>>x)&1) xs[nx++]=x;} else xs[nx++]=s;
  for(int a=0;a<nx;a++){ int st=xs[a];
   for(int t=0;t<nlib[p][st];t++){ Piece*q=&lib[p][st][t];
    int lo=(i==0||last)?tend:tmin; if(q->len<lo) break;
    if(q->mask&(bad|pv)) continue;
    if(!last && !((TM>>q->end)&1)) continue;
    int nt=total+q->len; ch[i]=q;
    occ[c]=q->mask;
    if(last){ if(nt>best){best=nt; dump(K,nt);} occ[c]=0; continue; }
    if(nt+ub(c,q->end)>best){
      for(int j=0;j<k;j++){int c2=c^(1<<j); if(vis[c2]) continue; if(i==0&&j>0) break;
        u32 e=1u<<q->end; int ok=1; for(int jj=0;jj<k;jj++){int c3=c2^(1<<jj); if(c3!=c&&(occ[c3]&e)){ok=0;break;}}
        if(ok) dfs(i+1,c2,q->end,nt);}
    }
    occ[c]=0;
    if(maxnodes&&nodes>maxnodes){vis[c]=0;return;}
   }
  }
  vis[c]=0;
}
int main(){
  if(scanf("%d %d %d %d %u %u %u %lld %d",&h,&k,&tmin,&tend,&AL[0],&AL[1],&TM,&maxnodes,&best)!=9) return 1;
  H=1<<h; K=1<<k; for(int x=0;x<H;x++){NB[x]=0; for(int d=0;d<h;d++) NB[x]|=1u<<(x^(1<<d));}
  for(int p=0;p<2;p++) for(int s=0;s<H;s++) if((AL[p]>>s)&1){cur[0]=s; gen(p,s,1,1u<<s,1u<<s); qsort(lib[p][s],nlib[p][s],sizeof(Piece),cmpl);}
  hk=calloc(HS,8); hv=calloc(HS,1);
  for(int p=0;p<2;p++){int n=0; for(int x=0;x<H;x++) n+=nlib[p][x]; flat[p]=malloc(4*(n+1)); flen[p]=malloc(n+1); int idx=0;
    for(int L=32;L>=1;L--) for(int x=0;x<H;x++) for(int t=0;t<nlib[p][x];t++) if(lib[p][x][t].len==L){flat[p][idx]=lib[p][x][t].mask; flen[p][idx++]=L;} nflat[p]=idx;}
  /* light symmetry: start cell 0 (translation of Q_k). */
  dfs(0,0,0,0);
  printf("END best %d nodes %lld %s\n",best,nodes,(maxnodes&&nodes>maxnodes)?"TRUNCATED":"COMPLETE");
}
