// Snakepit simulated annealing with cube-surgery proposals in Q_n (n<=10).
// State: induced linear forest F. Energy E = beta*|c-1| - v, c = v - e.
// Proposal: random subcube of dimension d in [dmin,dmax]; remove occupied
// vertices inside; greedy refill (pass 1: vertices touching fragments,
// pass 2: any addable vertex, followed by pass 1 again); one Metropolis test.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <stdint.h>
#include <time.h>

#define MAXN 10
static int N, NV;
static unsigned char occ[1<<MAXN], cnt[1<<MAXN];
static short nb[1<<MAXN][2];
static short oth[1<<MAXN];
static int V, E_;           // vertices, induced edges

static uint64_t s[4];
static inline uint64_t rotl(uint64_t x,int k){return (x<<k)|(x>>(64-k));}
static inline uint64_t rnd(void){uint64_t r=rotl(s[1]*5,7)*9,t=s[1]<<17;s[2]^=s[0];s[3]^=s[1];s[1]^=s[2];s[0]^=s[3];s[2]^=t;s[3]=rotl(s[3],45);return r;}
static inline double urand(void){return (rnd()>>11)*0x1.0p-53;}
static inline int rint_(int n){return (int)(((rnd()>>32)*(uint64_t)n)>>32);}

static inline int canadd(int x){
  if(occ[x]||cnt[x]>2) return 0;
  int a=-1,b=-1;
  for(int k=0;k<N;k++){int y=x^(1<<k); if(occ[y]){ if(cnt[y]>=2) return 0; if(a<0)a=y; else b=y; }}
  if(b>=0 && oth[a]==b) return 0;
  return 1;
}
static inline void link_(int u,int w){ nb[u][cnt[u]-1]=w; } // called after cnt incremented
static void add(int x){
  int a=-1,b=-1;
  for(int k=0;k<N;k++){int y=x^(1<<k); cnt[y]++; if(occ[y]){ if(a<0)a=y; else b=y; nb[y][cnt[y]-1]=x; }}
  occ[x]=1; V++;
  if(a<0){ oth[x]=x; }
  else if(b<0){ int ea=oth[a]; nb[x][0]=a; oth[x]=ea; oth[ea]=x; E_++; }
  else { int ea=oth[a], eb=oth[b]; nb[x][0]=a; nb[x][1]=b; oth[ea]=eb; oth[eb]=ea; E_+=2; }
}
static inline void unlink_(int u,int w){ if(nb[u][0]==w) nb[u][0]=nb[u][1]; }
static void rem(int x){
  int d=cnt[x];
  if(d==2){
    int a=nb[x][0], b=nb[x][1];
    // walk both sides alternately to find the end beyond a or beyond b
    int ca=a,pa=x,cb=b,pb=x, ea=-1, eb=-1;
    for(;;){
      if(cnt[ca]<2){ ea=ca; eb=oth[ca]; break; }
      if(cnt[cb]<2){ eb=cb; ea=oth[cb]; break; }
      int na = nb[ca][0]==pa? nb[ca][1]:nb[ca][0]; pa=ca; ca=na;
      int nn = nb[cb][0]==pb? nb[cb][1]:nb[cb][0]; pb=cb; cb=nn;
    }
    for(int k=0;k<N;k++){int y=x^(1<<k); if(occ[y]) unlink_(y,x); cnt[y]--; }
    occ[x]=0; V--; E_-=2;
    oth[a]=ea; oth[ea]=a; oth[b]=eb; oth[eb]=b;
  } else if(d==1){
    int a=nb[x][0], f=oth[x];
    for(int k=0;k<N;k++){int y=x^(1<<k); if(occ[y]) unlink_(y,x); cnt[y]--; }
    occ[x]=0; V--; E_--;
    oth[a]=f; oth[f]=a;
  } else {
    for(int k=0;k<N;k++){int y=x^(1<<k); cnt[y]--; }
    occ[x]=0; V--;
  }
}
static double BETA=3.0;
static inline double energy(void){ int c=V-E_; return BETA*abs(c-1) - V; }

static int remlist[1<<MAXN], addlist[1<<MAXN], nrem, nadd;
static int cube[1<<MAXN];

static int bestv=0;
static long long nprop=0;
static double t0;
static FILE *outf;
static int report_min=191;
static double now(){struct timespec ts;clock_gettime(CLOCK_MONOTONIC,&ts);return ts.tv_sec+1e-9*ts.tv_nsec;}

static int compbuf[1<<MAXN];
// largest component: returns size and writes its vertex sequence to compbuf
static int largest_comp(void){
  int best=0, bst=-1; static unsigned char seen[1<<MAXN]; memset(seen,0,NV);
  for(int u=0;u<NV;u++) if(occ[u]&&cnt[u]<=1&&!seen[u]){
    int p=-1,c=u,len=0; while(c>=0){ seen[c]=1; len++; int nx=-1; for(int j=0;j<cnt[c];j++) if(nb[c][j]!=p) nx=nb[c][j]; p=c;c=nx; }
    if(len>best){best=len;bst=u;}
  }
  if(bst>=0){ int p=-1,c=bst,i=0; while(c>=0){ compbuf[i++]=c; int nx=-1; for(int j=0;j<cnt[c];j++) if(nb[c][j]!=p) nx=nb[c][j]; p=c;c=nx; } }
  return best;
}
static void dump_comp(const char*tag,int L){
  fprintf(outf,"%s v=%d edges=%d t=%.2f prop=%lld :",tag,L,L-1,now()-t0,nprop);
  for(int i=0;i<L;i++) fprintf(outf," %d",compbuf[i]);
  fprintf(outf,"\n"); fflush(outf);
}
static void dump_snake(const char*tag){
  // walk from an endpoint
  int st=-1; for(int u=0;u<NV;u++) if(occ[u]&&cnt[u]<=1){st=u;break;}
  fprintf(outf,"%s v=%d edges=%d t=%.2f prop=%lld :",tag,V,V-1,now()-t0,nprop);
  int p=-1,c=st; for(int i=0;i<V;i++){ fprintf(outf," %d",c); int nx=-1; for(int j=0;j<cnt[c];j++) if(nb[c][j]!=p) nx=nb[c][j]; p=c; c=nx; if(c<0)break; }
  fprintf(outf,"\n"); fflush(outf);
}

int main(int argc,char**argv){
  N=9; uint64_t seed=1; double T0=1.0,T1=0.2; long long steps=100000000LL, cyc=0; int dmin=2,dmax=4; double tlimit=1e18;
  const char*init=NULL; const char*outname=NULL; int pass2_iso=1; int cmaxchk=4; double B0=0,B1=0; long long trace=0;
  for(int i=1;i<argc;i++){
    if(!strcmp(argv[i],"-n")) N=atoi(argv[++i]);
    else if(!strcmp(argv[i],"-s")) seed=strtoull(argv[++i],0,10);
    else if(!strcmp(argv[i],"-T0")) T0=atof(argv[++i]);
    else if(!strcmp(argv[i],"-T1")) T1=atof(argv[++i]);
    else if(!strcmp(argv[i],"-b")) BETA=atof(argv[++i]);
    else if(!strcmp(argv[i],"-steps")) steps=atoll(argv[++i]);
    else if(!strcmp(argv[i],"-cyc")) cyc=atoll(argv[++i]);
    else if(!strcmp(argv[i],"-dmin")) dmin=atoi(argv[++i]);
    else if(!strcmp(argv[i],"-dmax")) dmax=atoi(argv[++i]);
    else if(!strcmp(argv[i],"-t")) tlimit=atof(argv[++i]);
    else if(!strcmp(argv[i],"-init")) init=argv[++i];
    else if(!strcmp(argv[i],"-o")) outname=argv[++i];
    else if(!strcmp(argv[i],"-trace")) trace=atoll(argv[++i]);
    else if(!strcmp(argv[i],"-nopass2")) pass2_iso=0;
    else if(!strcmp(argv[i],"-B")) {B0=atof(argv[++i]);B1=atof(argv[++i]);BETA=B0;}
    else if(!strcmp(argv[i],"-cchk")) cmaxchk=atoi(argv[++i]);
    else if(!strcmp(argv[i],"-r")) report_min=atoi(argv[++i]);
  }
  NV=1<<N;
  s[0]=seed*0x9E3779B97F4A7C15ULL+1; s[1]=seed^0xD1B54A32D192ED03ULL; s[2]=0x8CB92BA72F3D8DD7ULL+seed*3; s[3]=0xABCDEF12345ULL^(seed<<7);
  for(int i=0;i<20;i++) rnd();
  outf = outname? fopen(outname,"a"): stdout;
  if(init){ FILE*f=fopen(init,"r"); int x; while(fscanf(f,"%d",&x)==1){ if(canadd(x)) add(x); } fclose(f); }
  t0=now();
  double E=energy();
  long long period = cyc>0? cyc: steps;
  int lastbest_print=0;
  for(nprop=0;nprop<steps;nprop++){
    if((nprop&0xFFFF)==0 && now()-t0>tlimit) break;
    if(trace && (nprop%trace)==0){ fprintf(outf,"TR prop=%lld T=%.3f V=%d c=%d best=%d\n",nprop,T0*pow(T1/T0,(double)(nprop%period)/period),V,V-E_,bestv); fflush(outf);}
    double fr = (double)(nprop%period)/period;
    double T = T0*pow(T1/T0,fr);
    if(B1>0){ BETA = B0*pow(B1/B0,fr); E=energy(); }
    int d = dmin + rint_(dmax-dmin+1);
    // choose d distinct coordinates
    int mask=0; while(__builtin_popcount(mask)<d) mask|=1<<rint_(N);
    int base = rint_(NV) & ~mask;
    int nc=0; for(int sub=mask;;sub=(sub-1)&mask){ cube[nc++]=base|sub; if(!sub)break; }
    // shuffle
    for(int i=nc-1;i>0;i--){int j=rint_(i+1);int t=cube[i];cube[i]=cube[j];cube[j]=t;}
    nrem=0; nadd=0;
    for(int i=0;i<nc;i++) if(occ[cube[i]]){ rem(cube[i]); remlist[nrem++]=cube[i]; }
    // pass 1
    int ch=1; while(ch){ ch=0; for(int i=0;i<nc;i++){int u=cube[i]; if(cnt[u]>=1&&canadd(u)){add(u);addlist[nadd++]=u;ch=1;}} }
    if(pass2_iso){ for(int i=0;i<nc;i++){int u=cube[i]; if(canadd(u)){add(u);addlist[nadd++]=u;
        int c2=1; while(c2){c2=0; for(int j=0;j<nc;j++){int w=cube[j]; if(cnt[w]>=1&&canadd(w)){add(w);addlist[nadd++]=w;c2=1;}}}}} }
    double En=energy(); double dE=En-E;
    if(dE<=0 || urand()<exp(-dE/T)){ E=En; 
      int c=V-E_;
      if(c==1){ if(V>bestv){ bestv=V; if(V>=report_min) dump_snake("BEST"); } }
      else if(c<=cmaxchk && V-(c-1)>bestv){ int L=largest_comp(); if(L>bestv){ bestv=L; if(L>=report_min) dump_comp("BEST",L);} }
    } else {
      for(int i=nadd-1;i>=0;i--) rem(addlist[i]);
      for(int i=nrem-1;i>=0;i--) add(remlist[i]);
    }
  }
  fprintf(outf,"END seed=%llu best_v=%d best_edges=%d time=%.2f props=%lld rate=%.3g/s\n",(unsigned long long)seed,bestv,bestv-1,now()-t0,nprop,nprop/(now()-t0));
  return 0;
}
