/* Symmetry-restricted snakepit annealing with cube surgery in Q_n.
 * State: an induced linear forest S (max degree 2, no cycles) that is invariant
 * under a fixed involution sigma(x) = pi(x) ^ t of Q_n (pi a coordinate
 * permutation with pi^2 = id, pi(t) = t). Moves add/remove whole sigma-orbits.
 * A sigma-invariant snake is reversed by sigma, so the search space is roughly
 * the square root of the unrestricted one. Energy E = beta*|c-1| - v.
 * Move: pick a random subcube of dimension dmin..dmax, remove every orbit meeting
 * it, refill greedily (two passes, random order), one Metropolis decision.
 * Also reports the longest single component when c is small (that component need
 * not be symmetric but is a valid snake).
 * usage: sym -n 9 -s SEED [-t secs] [-b beta] [-T temp] [-dmin 2 -dmax 4]
 *            [-perm p0,..,p{n-1} -x mask | (random involution from seed)]
 *            [-r report_min_edges] [-o out]
 * output: "SIGMA perm=.. x=.." then "BEST v=.. edges=.. t=.. : v0 v1 ..." lines and END.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <time.h>
static int N=9, V; static int perm[16]; static int tx=0;
static unsigned long long rs[4];
static unsigned long long rotl(unsigned long long x,int k){return (x<<k)|(x>>(64-k));}
static unsigned long long rnd(void){unsigned long long r=rotl(rs[1]*5,7)*9,t=rs[1]<<17;rs[2]^=rs[0];rs[3]^=rs[1];rs[1]^=rs[2];rs[0]^=rs[3];rs[2]^=t;rs[3]=rotl(rs[3],45);return r;}
static double urand(void){return (rnd()>>11)*(1.0/9007199254740992.0);}
static int sig[1024]; static unsigned char occ[1024]; static int deg[1024];
static int nv=0, ne=0;
static int applys(int x){int y=0;for(int i=0;i<N;i++) if(x>>i&1) y|=1<<perm[i]; return y^tx;}
static double now(void){struct timespec ts;clock_gettime(CLOCK_MONOTONIC,&ts);return ts.tv_sec+1e-9*ts.tv_nsec;}
static void addv(int u){occ[u]=1;nv++;ne+=deg[u];for(int i=0;i<N;i++)deg[u^(1<<i)]++;}
static void remv(int u){occ[u]=0;nv--;ne-=deg[u];for(int i=0;i<N;i++)deg[u^(1<<i)]--;}
/* walk component of u; returns 1 if it is a cycle */
static int iscycle(int u){
  if(deg[u]!=2) return 0;
  int prev=-1,cur=u,steps=0;
  while(1){ int nx=-1; for(int i=0;i<N;i++){int w=cur^(1<<i); if(occ[w]&&w!=prev){nx=w;break;}}
    if(nx<0) return 0; if(deg[nx]<2) return 0; prev=cur;cur=nx; if(cur==u) return 1; if(++steps>V) return 0; }
}
/* try to add orbit of u; returns number added (0 if invalid) */
static int addorbit(int u,int*buf){
  int a=u,b=sig[u]; if(occ[a]||occ[b]) return 0;
  addv(a); if(b!=a) addv(b);
  int ok=1; int vs[2]={a,b}; int m=(b!=a)?2:1;
  for(int k=0;k<m&&ok;k++){int x=vs[k]; if(deg[x]>2) ok=0; for(int i=0;i<N&&ok;i++){int w=x^(1<<i); if(occ[w]&&deg[w]>2) ok=0;}}
  if(ok) for(int k=0;k<m&&ok;k++) if(iscycle(vs[k])) ok=0;
  if(!ok){ if(b!=a) remv(b); remv(a); return 0; }
  buf[0]=a; if(m==2) buf[1]=b; return m;
}
static int bestout=0; static FILE*out; static double t0;
static void report_components(int minedges){
  /* print every path component with edges > bestout */
  static unsigned char seen[1024]; memset(seen,0,V);
  for(int u=0;u<V;u++) if(occ[u]&&!seen[u]&&deg[u]<=1){
    static int path[1024]; int L=0,prev=-1,cur=u;
    while(cur>=0){ path[L++]=cur; seen[cur]=1; int nx=-1; for(int i=0;i<N;i++){int w=cur^(1<<i); if(occ[w]&&w!=prev){nx=w;break;}} prev=cur; cur=nx; }
    if(L-1>bestout && L-1>=minedges){ bestout=L-1;
      fprintf(out,"BEST v=%d edges=%d t=%.0f :",L,L-1,now()-t0); for(int k=0;k<L;k++) fprintf(out," %d",path[k]); fprintf(out,"\n"); fflush(out);}
    else if(L-1>bestout) bestout=L-1;
  }
}
int main(int argc,char**argv){
  unsigned long long seed=1; double tl=600,beta=4,T=0.65; int dmin=2,dmax=4,rmin=188; const char*on=NULL; const char*ps=NULL; int xset=0;
  for(int i=1;i<argc;i++){
    if(!strcmp(argv[i],"-n")) N=atoi(argv[++i]); else if(!strcmp(argv[i],"-s")) seed=strtoull(argv[++i],0,10);
    else if(!strcmp(argv[i],"-t")) tl=atof(argv[++i]); else if(!strcmp(argv[i],"-b")) beta=atof(argv[++i]);
    else if(!strcmp(argv[i],"-T")) T=atof(argv[++i]); else if(!strcmp(argv[i],"-dmin")) dmin=atoi(argv[++i]);
    else if(!strcmp(argv[i],"-dmax")) dmax=atoi(argv[++i]); else if(!strcmp(argv[i],"-r")) rmin=atoi(argv[++i]);
    else if(!strcmp(argv[i],"-o")) on=argv[++i]; else if(!strcmp(argv[i],"-perm")) ps=argv[++i];
    else if(!strcmp(argv[i],"-x")) {tx=atoi(argv[++i]); xset=1;}
  }
  V=1<<N; rs[0]=seed*0x9E3779B97F4A7C15ULL+1; rs[1]=seed^0xD1B54A32D192ED03ULL; rs[2]=0x1234567; rs[3]=seed*7+3; for(int i=0;i<20;i++) rnd();
  out=on?fopen(on,"a"):stdout;
  for(int i=0;i<N;i++) perm[i]=i;
  if(ps){ int k=0; const char*p=ps; while(*p&&k<N){perm[k++]=atoi(p); while(*p&&*p!=',')p++; if(*p)p++;} if(!xset) tx=0; }
  else { /* random involution: k transpositions (0..4), t constant on pi-orbits, not identity */
    do{ for(int i=0;i<N;i++) perm[i]=i; int k=rnd()%5; int idx[16]; for(int i=0;i<N;i++) idx[i]=i;
      for(int i=N-1;i>0;i--){int j=rnd()%(i+1);int z=idx[i];idx[i]=idx[j];idx[j]=z;}
      for(int j=0;j<k;j++){perm[idx[2*j]]=idx[2*j+1]; perm[idx[2*j+1]]=idx[2*j];}
      tx=0; for(int i=0;i<N;i++) if(perm[i]>=i && (rnd()&1)) { tx|=1<<i; tx|=1<<perm[i]; }
      int id=(tx==0); for(int i=0;i<N;i++) if(perm[i]!=i) id=0;
      /* a sigma-reversed snake needs a centre: a fixed vertex or an x with sigma(x) adjacent to x */
      int centre=0; for(int x=0;x<(1<<N)&&!centre;x++) if(__builtin_popcount(applys(x)^x)<=1) centre=1;
      if(!id && centre) break; }while(1);
  }
  for(int x=0;x<V;x++){ sig[x]=applys(x); }
  for(int x=0;x<V;x++) if(sig[sig[x]]!=x){fprintf(stderr,"not an involution\n");return 1;}
  int nfix=0; for(int x=0;x<V;x++) nfix+=(sig[x]==x);
  fprintf(out,"SIGMA perm="); for(int i=0;i<N;i++) fprintf(out,"%d%s",perm[i],i<N-1?",":""); fprintf(out," x=%d fixed=%d seed=%llu\n",tx,nfix,seed); fflush(out);
  memset(occ,0,sizeof occ); memset(deg,0,sizeof deg);
  static int order[1024]; for(int i=0;i<V;i++) order[i]=i;
  for(int i=V-1;i>0;i--){int j=rnd()%(i+1);int z=order[i];order[i]=order[j];order[j]=z;}
  int buf[2]; for(int i=0;i<V;i++) addorbit(order[i],buf);
  t0=now(); long long props=0; double E=beta*fabs(nv-ne-1.0)-nv;
  static int remd[1024], addd[1024], cand[64];
  while(1){
    if((props&1023)==0 && now()-t0>tl) break;
    props++;
    int d=dmin+rnd()%(dmax-dmin+1); int mask=0; while(__builtin_popcount(mask)<d) mask|=1<<(rnd()%N);
    int base=rnd()%V & ~mask; int nc=0;
    for(int s=mask;;s=(s-1)&mask){ cand[nc++]=base|s; if(!s) break; }
    int nr=0,na=0;
    for(int k=0;k<nc;k++){int u=cand[k]; if(occ[u]){ remv(u); remd[nr++]=u; int w=sig[u]; if(w!=u&&occ[w]){remv(w); remd[nr++]=w;} }}
    for(int pass=0;pass<2;pass++){
      for(int k=nc-1;k>0;k--){int j=rnd()%(k+1);int z=cand[k];cand[k]=cand[j];cand[j]=z;}
      for(int k=0;k<nc;k++){int m=addorbit(cand[k],buf); for(int q=0;q<m;q++) addd[na++]=buf[q];}
    }
    double En=beta*fabs(nv-ne-1.0)-nv, dE=En-E;
    if(dE<=0 || urand()<exp(-dE/T)){ E=En; }
    else { for(int k=na-1;k>=0;k--) remv(addd[k]); for(int k=nr-1;k>=0;k--) addv(remd[k]); }
    int c=nv-ne; if(c<=4 && ne>bestout) report_components(rmin);
  }
  fprintf(out,"END seed=%llu best_edges=%d time=%.0f props=%lld rate=%.0f\n",seed,bestout,now()-t0,props,props/(now()-t0));
  return 0;
}
