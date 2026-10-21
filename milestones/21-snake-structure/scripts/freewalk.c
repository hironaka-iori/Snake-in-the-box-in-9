/* Exhaustive branch and bound over the family "palette, free quotient walk":
   Q_{h+k} = Q_h x Q_k, cells may be revisited (at most V visits in total).
   Even cells use heavy vertices in AL[0], odd cells AL[1]; light transitions
   only at heavy vertices in TM.  Interior pieces have >= tmin vertices.
   Finds a snake with more than `best` vertices or proves none exists
   (COMPLETE), unless the node limit is hit (TRUNCATED).
   stdin: h k V tmin AL0 AL1 TM maxnodes best */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
typedef uint32_t u32;
static int h,k,V,tmin,H,K,best; static u32 AL[2],TM,NB[32]; static long long nodes=0,maxnodes;
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
static int LFC[2];
static u32 closedm(u32 s){u32 r=s; for(int x=0;x<H;x++) if((s>>x)&1) r|=NB[x]; return r;}
static int is_lf(u32 S){ /* induced linear forest: max degree 2 and acyclic */
  int e=0; for(int x=0;x<H;x++) if((S>>x)&1){int d=__builtin_popcount(NB[x]&S); if(d>2) return 0; e+=d;} e/=2;
  /* components */ u32 rem=S; int comp=0; while(rem){ u32 fr=rem&-rem, seen=fr; while(fr){int x=__builtin_ctz(fr); fr&=fr-1; u32 nw=NB[x]&S&~seen; seen|=nw; fr|=nw;} rem&=~seen; comp++; }
  return e==__builtin_popcount(S)-comp; }
static int lfmax(u32 al){ /* brute force over subsets of al (<= 2^22) */
  int n=__builtin_popcount(al), idx[32], t=0; for(int x=0;x<H;x++) if((al>>x)&1) idx[t++]=x;
  int bestv=0; for(long s=0;s<(1L<<n);s++){ int c=__builtin_popcountl(s); if(c<=bestv) continue; u32 S=0; for(int i=0;i<n;i++) if((s>>i)&1) S|=1u<<idx[i]; if(is_lf(S)) bestv=c; } return bestv; }
static u32 occ[64]; static int nv=0; static int vc[64]; static Piece* ch[256]; static int cc_[256];
static void dump(int n,int total){ printf("BEST %d :",total); for(int i=0;i<n;i++){printf(" [c%d:",cc_[i]); for(int z=0;z<ch[i]->len;z++) printf("%s%d",z?",":"",ch[i]->seq[z]); printf("]");} printf("\n"); fflush(stdout);}
static int ub(int c,int e){ int t=0; for(int c2=0;c2<K;c2++){ u32 fr=AL[par(c2)]&~closedm(occ[c2]);
    for(int j=0;j<k;j++){int c3=c2^(1<<j); fr&=~(c3==c? (occ[c3]&~(1u<<e)) : occ[c3]);}
    int a=__builtin_popcount(fr), b=LFC[par(c2)]-__builtin_popcount(occ[c2]); t+= a<b?a:b; } return t; }
static void dfs(int i,int c,int s,int prev,int total){
  if(maxnodes&&nodes>maxnodes) return; nodes++;
  int p=par(c);
  u32 bad=closedm(occ[c]); for(int j=0;j<k;j++){int c2=c^(1<<j); if(c2!=prev) bad|=occ[c2];}
  u32 pv= i? occ[prev]&~(1u<<s):0;
  int xs[32],nx=0; if(i==0){for(int x=0;x<H;x++) if((AL[p]>>x)&1) xs[nx++]=x;} else xs[nx++]=s;
  for(int a=0;a<nx;a++){ int st=xs[a];
   for(int t=0;t<nlib[p][st];t++){ Piece*q=&lib[p][st][t];
    if(q->mask&(bad|pv)) continue;
    int nt=total+q->len; ch[i]=q; cc_[i]=c;
    if(nt>best){best=nt; dump(i+1,nt);}            /* path may end here */
    if(i+1>=V || q->len<tmin || !((TM>>q->end)&1)) continue;
    occ[c]|=q->mask;
    if(nt+ub(c,q->end)>best){
      for(int j=0;j<k;j++){ if(i==0&&j>0) break; int c2=c^(1<<j);
        u32 e=1u<<q->end; if(closedm(occ[c2])&e) continue;
        int ok=1; for(int jj=0;jj<k;jj++){int c3=c2^(1<<jj); if(c3!=c&&(occ[c3]&e)){ok=0;break;}}
        if(ok) dfs(i+1,c2,q->end,c,nt);}
    }
    occ[c]&=~q->mask;
    if(maxnodes&&nodes>maxnodes) return;
   }
  }
}
int main(){
  if(scanf("%d %d %d %d %u %u %u %lld %d",&h,&k,&V,&tmin,&AL[0],&AL[1],&TM,&maxnodes,&best)!=9) return 1;
  H=1<<h; K=1<<k; for(int x=0;x<H;x++){NB[x]=0; for(int d=0;d<h;d++) NB[x]|=1u<<(x^(1<<d));}
  for(int p=0;p<2;p++) for(int s=0;s<H;s++) if((AL[p]>>s)&1){cur[0]=s; gen(p,s,1,1u<<s,1u<<s); qsort(lib[p][s],nlib[p][s],sizeof(Piece),cmpl);}
  LFC[0]=lfmax(AL[0]); LFC[1]=lfmax(AL[1]); fprintf(stderr,"LF caps %d %d\n",LFC[0],LFC[1]);
  int b0=best;
  dfs(0,0,0,-1,0);
  printf("END init %d best %d nodes %lld %s\n",b0,best,nodes,(maxnodes&&nodes>maxnodes)?"TRUNCATED":"COMPLETE");
}
