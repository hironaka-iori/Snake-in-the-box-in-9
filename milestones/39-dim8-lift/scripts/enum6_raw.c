/* Enumerate the induced linear forests of Q_k (k <= 6) with at least T vertices, up to the
   hyperoctahedral group B_k (translations x coordinate permutations), by brute-force canonical
   form (minimum 64-bit mask over the group).  Output: one line per orbit: size paths mask(hex).
   usage: enumk k T                                                                          */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef unsigned long long u64;
static int k, V, T;
static int in[64], deg[64], par[64], perms[720][6], np;
static int find(int x){ while(par[x]!=x) x=par[x]; return x; }
static u64 *seen; static long nseen, cap;
static int pmap[720][64];
static int bestp, bestt;
static u64 canon(u64 m){
  u64 best = ~0ULL;
  for(int p=0;p<np;p++){
    u64 pm=0; for(int u=0;u<V;u++) if(m>>u&1) pm|=1ULL<<pmap[p][u];
    for(int t=0;t<V;t++){ u64 r=0; u64 x=pm; while(x){ int u=__builtin_ctzll(x); x&=x-1; r|=1ULL<<(u^t);} if(r<best){ best=r; bestp=p; bestt=t; } }
  }
  return best;
}
static long long raw=0;
static int countonly; static int rawmode=1;
static void emit(void){
  if(countonly){ raw++; return; }
  u64 m=0; int sz=0, e=0; for(int u=0;u<V;u++) if(in[u]){ m|=1ULL<<u; sz++; e+=deg[u]; }
  raw++;
  /* cheap pre-filter: only canonicalize when m is lexicographically... (no) */
  u64 c=canon(m);
  if(rawmode){ printf("R %016llx %016llx %d %d\n",(unsigned long long)m,(unsigned long long)c,bestp,bestt); }
  /* linear-probe hash set */
  u64 h=(c*0x9E3779B97F4A7C15ULL)>>20; h%=cap;
  while(seen[h]){ if(seen[h]==c+1) return; h=(h+1)%cap; }
  seen[h]=c+1; nseen++;
  if(!rawmode) printf("%d %d %016llx\n", sz, sz-e/2, (unsigned long long)c);
  if(nseen*2>cap){ fprintf(stderr,"hash full\n"); exit(1);} 
}
static int cur=0; static u64 forceA; static int forcing, amax, amax_cnt_a;
static int blk[4];
static void rec(int v){
  { int b=v>>4, r=16-(v&15); int cap=8-blk[b]; if(cap>r) cap=r; int bound=cur+cap+8*((V>>4)-b-1); if(v==V) bound=cur; if(bound<T) return; }
  if(v==V){ emit(); return; }
  if(!(forcing && v<V/2 && (forceA>>v&1))) rec(v+1);
  if(forcing && v<V/2 && !(forceA>>v&1)) return;
  if(forcing && v>=V/2 && cur - amax_cnt_a >= amax) return;
  int nb[8],m=0; for(int i=0;i<k;i++){int u=v^(1<<i); if(u<v && in[u]) nb[m++]=u;}
  if(m>2) return;
  for(int j=0;j<m;j++) if(deg[nb[j]]>=2) return;
  int r[2]; for(int j=0;j<m;j++) r[j]=find(nb[j]);
  if(m==2 && r[0]==r[1]) return;
  in[v]=1; deg[v]=m; cur++; blk[v>>4]++; for(int j=0;j<m;j++) deg[nb[j]]++;
  par[v]=v; int old[2]; for(int j=0;j<m;j++){old[j]=r[j]; par[r[j]]=v;}
  rec(v+1);
  for(int j=0;j<m;j++) par[old[j]]=old[j];
  in[v]=0; deg[v]=0; cur--; blk[v>>4]--; for(int j=0;j<m;j++) deg[nb[j]]--;
}
static int a[6], used[6];
static void genp(int i){ if(i==k){ memcpy(perms[np++],a,sizeof a); return;} for(int j=0;j<k;j++) if(!used[j]){used[j]=1;a[i]=j;genp(i+1);used[j]=0;} }
int main(int argc,char**argv){
  k=atoi(argv[1]); T=atoi(argv[2]); countonly=(argc>3 && argv[3][0]=='x'); V=1<<k; for(int i=0;i<V;i++) par[i]=i;
  genp(0);
  for(int p=0;p<np;p++) for(int u=0;u<V;u++){ int w=0; for(int i=0;i<k;i++) if(u>>i&1) w|=1<<perms[p][i]; pmap[p][u]=w; }
  cap = 1<<24; seen=calloc(cap,sizeof(u64));
  if(argc>4){ /* forcing mode: argv[4] = file of 'size pieces hexmask' Q_{k-1} reps */
    forcing=1; FILE*f=fopen(argv[4],"r"); int sz,p; unsigned long long h;
    while(fscanf(f,"%d %d %llx",&sz,&p,&h)==3){ if(sz < (T+1)/2) continue; forceA=h; amax=sz; amax_cnt_a=sz; rec(0); }
    fclose(f);
  } else rec(0);
  fprintf(stderr,"k=%d T=%d raw=%lld orbits=%ld\n",k,T,raw,nseen);
}
