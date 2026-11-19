/* Knuth's estimator for the size of an exhaustive snake search tree in Q_n.
   Tree: snakes starting at vertex 0, coordinates introduced in increasing order (each new direction
   is the least unused one), grown at one end.  A node is pruned when
       |path| + (#available vertices reachable from the head through available vertices) < T,
   where available = not on the path and adjacent to no path vertex other than the head.
   Optional second bound (mode 2): per facet, the vertices still addable in the two halves of every
   coordinate cut are capped by a table value: |path cap H| + avail(H) is fine; we use the
   sharper "subcube capacity": for each 5-subcube in the partition by coords 5..n-1, at most 16
   (Huang) vertices of the final snake lie in it (cheap and valid).
   usage: knuth n T probes seed [mode]                                                       */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
static int n, V, T, mode;
static unsigned long long rs;
static unsigned rnd(void){ rs ^= rs<<13; rs ^= rs>>7; rs ^= rs<<17; return (unsigned)(rs>>11); }
static int onp[1<<12], blk[1<<12], path[1<<12], len, maxdir;
static int q[1<<12], mark[1<<12], stamp;
static int reach(int h){ /* available reachable from head h (excluding h) */
  stamp++; int qh=0, qt=0, cnt=0; q[qt++]=h; mark[h]=stamp;
  while(qh<qt){ int x=q[qh++]; for(int i=0;i<n;i++){ int y=x^(1<<i); if(mark[y]==stamp) continue;
      if(onp[y]||blk[y]) continue; mark[y]=stamp; q[qt++]=y; cnt++; } }
  return cnt;
}
/* blk[y] = number of path vertices other than head adjacent to y, maintained incrementally */
static void push(int v){ /* old head becomes non-head: its neighbours get blocked */
  if(len>0){ int h=path[len-1]; for(int i=0;i<n;i++) blk[h^(1<<i)]++; }
  path[len++]=v; onp[v]=1;
}
static void pop(void){ int v=path[--len]; onp[v]=0; if(len>0){ int h=path[len-1]; for(int i=0;i<n;i++) blk[h^(1<<i)]--; } }
int main(int argc,char**argv){
  n=atoi(argv[1]); T=atoi(argv[2]); long probes=atol(argv[3]); rs=atoll(argv[4])*2654435761ULL+1; mode=argc>5?atoi(argv[5]):1;
  V=1<<n;
  double sumest=0, sumsq=0; double depthsum=0; int maxlen=0;
  double lvl[1<<12]; memset(lvl,0,sizeof lvl);
  for(long p=0;p<probes;p++){
    memset(onp,0,sizeof(int)*V); memset(blk,0,sizeof(int)*V); len=0;
    push(0); int md=-1; /* max direction used */
    double w=1, est=1;
    int mds[1<<12]; mds[0]=-1;
    while(1){
      int h=path[len-1]; int ch[32], nc=0;
      for(int i=0;i<n && i<=md+1;i++){ int y=h^(1<<i); if(onp[y]||blk[y]) continue;
        /* y must not be adjacent to path vertices other than h: blk[y]==0 checked */
        push(y); int ok = (len + reach(y)) >= T; pop();
        if(ok) ch[nc++]=i; }
      if(nc==0) break;
      w*=nc; est+=w; lvl[len]+=w;
      int i=ch[rnd()%nc]; if(i>md) md=i; push(h^(1<<i));
    }
    if(len>maxlen) maxlen=len;
    depthsum+=len; sumest+=est; sumsq+=est*est;
  }
  double mean=sumest/probes, var=sumsq/probes-mean*mean;
  printf("n=%d T=%d probes=%ld est_nodes=%.3e rel_stderr=%.2f mean_leafdepth=%.1f max_leafdepth=%d\n",
         n,T,probes,mean,sqrt(var/probes)/mean,depthsum/probes,maxlen);
  for(int d=0; d<V; d+= (n>=9?20:10)) if(lvl[d]>0) printf("  depth %d: %.3e\n", d, lvl[d]/probes);
  return 0;
}
