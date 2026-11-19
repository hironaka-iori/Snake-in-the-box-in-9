// Wang-Landau estimate of N(L) = number of directed snakes (vertex sequences)
// with L edges in Q_n, via end moves (add/remove at either end), MH-corrected.
// Normalisation: N(0) = 2^n. Output: L lnN(L) visits.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <stdint.h>
#include <time.h>
static int N,NV; static unsigned char occ[1024],cnt[1024];
static int buf[4096]; static int head,len; // path = buf[head..head+len-1] (mod 4096)
static uint64_t s[2];
static inline uint64_t rnd(void){uint64_t s1=s[0];const uint64_t s0=s[1];s[0]=s0;s1^=s1<<23;s[1]=s1^s0^(s1>>17)^(s0>>26);return s[1]+s0;}
static inline double urand(void){return (rnd()>>11)*0x1.0p-53;}
#define AT(i) buf[((i)+4096)&4095]
static void put(int y){occ[y]=1;for(int k=0;k<N;k++)cnt[y^(1<<k)]++;}
static void take(int y){occ[y]=0;for(int k=0;k<N;k++)cnt[y^(1<<k)]--;}
static double now(){struct timespec t;clock_gettime(CLOCK_MONOTONIC,&t);return t.tv_sec+1e-9*t.tv_nsec;}
int main(int argc,char**argv){
  N=atoi(argv[1]); int Lmax=atoi(argv[2]); double tl=atof(argv[3]); uint64_t seed=argc>4?atoll(argv[4]):1;
  NV=1<<N; s[0]=seed*0x9E3779B97F4A7C15ULL|1; s[1]=0x1234567ULL^seed;
  double *lg=calloc(Lmax+1,8); long long *H=calloc(Lmax+1,8), *tot=calloc(Lmax+1,8);
  head=2048; len=1; buf[head]=0; put(0);
  double lnf=1.0, t0=now(); long long it=0; int L=0, top=0;
  while(now()-t0<tl){
    for(int rep=0;rep<1000000;rep++){
      it++;
      int front = rnd()&1, addm = rnd()&1;
      int L0=len-1;
      if(addm){
        if(L0>=Lmax) goto rec;
        int e = front? AT(head): AT(head+len-1);
        int y = e ^ (1<<(rnd()%N));
        if(occ[y] || cnt[y]!=1) goto rec;   // must touch only e
        double a = lg[L0]-lg[L0+1] + log((double)N);
        if(a<0 && urand()>=exp(a)) goto rec;
        put(y); if(front){head--; AT(head)=y;} else AT(head+len)=y; len++;
      } else {
        if(L0==0) goto rec;
        double a = lg[L0]-lg[L0-1] - log((double)N);
        if(a<0 && urand()>=exp(a)) goto rec;
        int y; if(front){y=AT(head); head++;} else y=AT(head+len-1); len--; take(y);
      }
    rec:
      L=len-1; lg[L]+=lnf; H[L]++; tot[L]++; if(L>top)top=L;
    }
    // flatness over visited range [0,top]
    long long mn=-1; double mean=0; for(int i=0;i<=top;i++){mean+=H[i]; if(mn<0||H[i]<mn)mn=H[i];}
    mean/= (top+1);
    if(mn > 0.8*mean && lnf>1e-7){ lnf*=0.5; memset(H,0,8*(Lmax+1)); }
  }
  fprintf(stderr,"it=%lld lnf=%g top=%d\n",it,lnf,top);
  for(int i=0;i<=top;i++) printf("%d %.6f %lld\n",i,lg[i]-lg[0]+N*log(2.0),tot[i]);
}
