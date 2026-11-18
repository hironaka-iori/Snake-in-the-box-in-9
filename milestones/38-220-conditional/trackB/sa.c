/* Simulated annealing for low-weight local configurations of a window (track B ceilings).
   stdin: n (window length) then n vertices (path x_0..x_{n-1}), radius R, M, wA, iters, seed, mode
   mode 0: objective = sum over centres 1..n-2 of (wA*alpha + share_M)
   Constraints (as wincert.Encoding): window selected; every selected vertex has <= 2 selected
   neighbours; interior (all 9 nbrs in ball) selected vertices have >= 1, at most 2 have exactly 1;
   no cycle inside the ball (checked on output, penalised via 4-cycle/6-cycle local check + final).
   Output: best objective and the selection (ball vertices selected). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
static int n, R, M, wA, win[64], inball[512], dist[512], sel[512], fixed_[512], interior[512];
static int ball[512], nb;
static unsigned long long rs;
static double rnd(void){ rs ^= rs<<13; rs ^= rs>>7; rs ^= rs<<17; return (rs>>11)*(1.0/9007199254740992.0);}
static int deg(int v){int d=0; for(int k=0;k<9;k++) d+=sel[v^(1<<k)]; return d;}
static int used_dir(int ci,int k){ return ((win[ci]^win[ci-1])==(1<<k)) || ((win[ci]^win[ci+1])==(1<<k)); }
static long objective(long *A, long *S){
  long a=0,s=0;
  for(int ci=1;ci<n-1;ci++){int c=win[ci];
    for(int p=0;p<9;p++) if(!used_dir(ci,p)) for(int q=p+1;q<9;q++) if(!used_dir(ci,q)) if(!sel[c^(1<<p)^(1<<q)]) a++;
    for(int k=0;k<9;k++){ if(used_dir(ci,k)) continue; int u=c^(1<<k); if(sel[u]) continue;
      int e0=0; for(int p=0;p<9;p++) for(int q=p+1;q<9;q++){ if(!(sel[u^(1<<p)]||sel[u^(1<<q)]||sel[u^(1<<p)^(1<<q)])) e0++; }
      int d=deg(u); s += (M*e0)/d; }
  }
  *A=a; *S=s; return wA*a+s;
}
/* local validity after flipping v on: degrees of v and its nbrs <= 2, no selected square containing v */
static int ok_on(int v){
  if(deg(v)>2) return 0;
  for(int k=0;k<9;k++){int u=v^(1<<k); if(sel[u] && deg(u)>2) return 0;}
  for(int p=0;p<9;p++) for(int q=p+1;q<9;q++){ if(sel[v^(1<<p)]&&sel[v^(1<<q)]&&sel[v^(1<<p)^(1<<q)]) return 0; }
  return 1;
}
static int penalty(void){ /* interior isolated count*10 + max(0, deg1 interior -2)*10 */
  int iso=0,d1=0; for(int i=0;i<nb;i++){int v=ball[i]; if(!sel[v]||!interior[v]) continue; int d=deg(v); if(d==0) iso++; if(d==1) d1++;}
  return 10*iso + 10*(d1>2?d1-2:0);
}
/* cycle detection: any component with all degrees 2 inside ball (selected outside ball are 0) */
static int has_cycle(void){ static int seen[512]; memset(seen,0,sizeof seen);
  for(int i=0;i<nb;i++){int v=ball[i]; if(!sel[v]||seen[v]) continue;
    int st[512],sp=0,allow=1,cnt=0; st[sp++]=v; seen[v]=1;
    while(sp){int x=st[--sp]; cnt++; if(deg(x)!=2) allow=0; for(int k=0;k<9;k++){int u=x^(1<<k); if(sel[u]&&!seen[u]){seen[u]=1; st[sp++]=u;}}}
    if(allow) return 1; }
  return 0; }
int main(){
  long iters; unsigned long long seed; int mode;
  if(scanf("%d",&n)!=1) return 1; for(int i=0;i<n;i++) scanf("%d",&win[i]);
  scanf("%d %d %d %ld %llu %d",&R,&M,&wA,&iters,&seed,&mode); rs=seed*2654435761ULL+1;
  for(int v=0;v<512;v++){int dm=99; for(int i=0;i<n;i++){int d=__builtin_popcount(v^win[i]); if(d<dm) dm=d;} dist[v]=dm; inball[v]=dm<=R; if(inball[v]) ball[nb++]=v;}
  for(int v=0;v<512;v++){ interior[v]=0; if(!inball[v]) continue; int a=1; for(int k=0;k<9;k++) if(!inball[v^(1<<k)]) a=0; interior[v]=a; }
  for(int i=0;i<n;i++){ sel[win[i]]=1; fixed_[win[i]]=1; }
  { int ns=0; if(scanf("%d",&ns)==1){ for(int i=0;i<ns;i++){int v; if(scanf("%d",&v)==1 && inball[v]) sel[v]=1;} } }
  /* forbid neighbours of centres (they would get degree 3) */
  long A,S; long cur=objective(&A,&S); int pen=penalty(); double T0=getenv("T0")?atof(getenv("T0")):300.0, T1=getenv("T1")?atof(getenv("T1")):1.0;
  long best=1L<<40; static int bestsel[512];
  if(pen==0 && !has_cycle()){ best=cur; memcpy(bestsel,sel,sizeof sel); }
  for(long it=0; it<iters; it++){
    double T=T0*pow(T1/T0,(double)it/iters);
    int v=ball[(int)(rnd()*nb)]; if(fixed_[v]) continue;
    if(!sel[v]){ sel[v]=1; if(!ok_on(v)){ sel[v]=0; continue; } }
    else sel[v]=0;
    long nA,nS; long nw=objective(&nA,&nS); int np=penalty();
    double delta=(nw+np*50.0*wA)-(cur+pen*50.0*wA);
    if(delta<=0 || rnd()<exp(-delta/T)){ cur=nw; pen=np;
      if(pen==0 && cur<best && !has_cycle()){ best=cur; memcpy(bestsel,sel,sizeof sel); } }
    else sel[v]^=1;
  }
  fprintf(stderr,"final cur %ld pen %d cyc %d nb %d\n",cur,pen,has_cycle(),nb); printf("%ld\n",best); for(int i=0;i<nb;i++) if(bestsel[ball[i]]) printf("%d ",ball[i]); printf("\n");
  return 0;
}
