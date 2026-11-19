/* For each Q6 forest representative A (file of 'size pieces hexmask'), enumerate the induced
   linear forests B of the other half of Q7 = Q6 x Q1 such that A u (B + 64) is an induced linear
   forest of Q7 with lo <= |B| <= |A| where lo = T - |A|.  Prints per A: index count [and masks].
   usage: ext7 T reps.txt [dump]                                                              */
#include <stdio.h>
#include <stdlib.h>
typedef unsigned long long u64;
static int n=7, V=128, T, dump;
static int in[128], deg[128], par[128], blk[8], cur, asz;
static long long cnt;
static int find(int x){ while(par[x]!=x) x=par[x]; return x; }
static void rec(int v){
  if(v==V){ cnt++; if(dump){ u64 m=0; for(int u=64;u<128;u++) if(in[u]) m|=1ULL<<(u-64); printf(" %016llx",m);} return; }
  int b=v>>4, r=16-(v&15); int cap=8-blk[b]; if(cap>r) cap=r;
  int bsz=cur-asz;
  if(bsz + cap + 8*(7-b) < T-asz) return;
  rec(v+1);
  if(bsz>=asz) return;
  int nb[8],m=0; for(int i=0;i<n;i++){int u=v^(1<<i); if(u<v && in[u]) nb[m++]=u;}
  if(m>2) return;
  for(int j=0;j<m;j++) if(deg[nb[j]]>=2) return;
  int rr[2]; for(int j=0;j<m;j++) rr[j]=find(nb[j]);
  if(m==2 && rr[0]==rr[1]) return;
  in[v]=1; deg[v]=m; cur++; blk[b]++; for(int j=0;j<m;j++) deg[nb[j]]++;
  par[v]=v; int old[2]; for(int j=0;j<m;j++){old[j]=rr[j]; par[rr[j]]=v;}
  rec(v+1);
  for(int j=0;j<m;j++) par[old[j]]=old[j];
  in[v]=0; deg[v]=0; cur--; blk[b]--; for(int j=0;j<m;j++) deg[nb[j]]--;
}
int main(int argc,char**argv){
  T=atoi(argv[1]); dump=argc>3;
  FILE*f=fopen(argv[2],"r"); int sz,p,idx=0; u64 h; long long tot=0;
  while(fscanf(f,"%d %d %llx",&sz,&p,&h)==3){
    for(int i=0;i<V;i++){in[i]=0;deg[i]=0;par[i]=i;} for(int i=0;i<8;i++) blk[i]=0; cur=0;
    /* place A in vertices 0..63 (it is a forest of Q6, already valid) */
    for(int u=0;u<64;u++) if(h>>u&1){ in[u]=1; cur++; blk[u>>4]++; }
    for(int u=0;u<64;u++) if(in[u]) for(int i=0;i<6;i++){int w=u^(1<<i); if(in[w]){ deg[u]++; if(w<u){ int a=find(u), c=find(w); if(a!=c) par[a]=c; }}}
    asz=sz; cnt=0;
    if(dump) printf("%d %d %016llx", idx, sz, h);
    if(2*sz >= T) rec(64);
    if(dump) printf("\n"); else printf("%d %d %d %lld\n", idx, sz, p, cnt);
    fflush(stdout); tot+=cnt; idx++;
  }
  fprintf(stderr,"T=%d total=%lld\n",T,tot);
}
