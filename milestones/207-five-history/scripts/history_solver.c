/* Exact finite-domain search with residual-coordinate lexicographic pruning.
   Exhaustion is a native result. This program supplies no Lean certificate. */
#include <stdint.h>
#include <stddef.h>
/* Direct declarations for the Windows CRT and kernel API linked by leanc.
   The bundled compiler includes integer headers but no full CRT headers. */
extern int printf(const char *, ...);
extern int scanf(const char *, ...);
extern int puts(const char *);
extern int putchar(int);
extern void exit(int);
extern void *memcpy(void *, const void *, size_t);
extern void *memset(void *, int, size_t);
__declspec(dllimport) unsigned long long __stdcall GetTickCount64(void);
#define SCNu64 "llu"
#define PRIu64 "llu"

#define NMAX 128
#define DMAX 64
#define PMAX 120
#define GMAX 720
#define QCAP (NMAX*NMAX+1)
#define BIT(x) (UINT64_C(1) << (x))
static int n, size, nc, ng, np;
static uint64_t relation[NMAX][NMAX][DMAX], initial[NMAX];
static unsigned char adjacent[NMAX][NMAX], queued[NMAX][NMAX];
static int degree[NMAX], forbidden[GMAX][NMAX], solution[NMAX];
static uint64_t fixed_mask[PMAX], less_equal_mask[PMAX];
static unsigned queue[QCAP], head, tail;
static uint64_t nodes, removals, lex_removals, node_limit;
static unsigned long long started;
static double seconds_limit;

static void fail(const char *message) { puts(message); exit(3); }
static int read_int(void) { int v; if (scanf("%d", &v)!=1) fail("Missing integer"); return v; }
static uint64_t read_mask(void) {
  uint64_t v; if (scanf("%" SCNu64, &v)!=1) fail("Missing mask"); return v;
}
static void enqueue(int x, int y) {
  if (queued[x][y]) return;
  unsigned next=(tail+1)%QCAP;
  if (next==head) fail("Queue capacity exceeded");
  queue[tail]=(unsigned)(x*NMAX+y); tail=next; queued[x][y]=1;
}
static void changed(int x) {
  for (int z=0;z<n;z++) if (adjacent[z][x]) enqueue(z,x);
}
static int propagate(uint64_t *domains) {
  memset(queued,0,sizeof queued); head=tail=0;
  for (int x=0;x<n;x++) {
    if (!domains[x]) return 0;
    for (int y=0;y<n;y++) if (adjacent[x][y]) enqueue(x,y);
  }
  for (;;) {
    while (head!=tail) {
      unsigned pair=queue[head]; head=(head+1)%QCAP;
      int x=(int)(pair/NMAX),y=(int)(pair%NMAX);queued[x][y]=0;
      uint64_t before=domains[x], kept=0, scan=before;
      while (scan) {
        int u=__builtin_ctzll(scan);scan&=scan-1;
        if (relation[x][y][u]&domains[y]) kept|=BIT(u);
      }
      if (kept!=before) {
        removals+=(uint64_t)__builtin_popcountll(before^kept);domains[x]=kept;
        if (!kept) return 0;
        changed(x);
      }
    }
    int altered=0;
    for (int g=0;g<ng;g++) {
      int possible=1, free_count=0, last=-1;
      for (int x=0;x<n;x++) {
        if (!(domains[x]&BIT(forbidden[g][x]))) { possible=0; break; }
        if (domains[x]&(domains[x]-1)) { free_count++; last=x; }
      }
      if (!possible) continue;
      if (!free_count) return 0;
      if (free_count==1) {
        domains[last]&=~BIT(forbidden[g][last]);removals++;altered=1;
        if (!domains[last]) return 0;
        changed(last);
      }
    }
    /* Every earlier domain must consist entirely of words fixed by this
       permutation before a later lexicographic comparison is forced. */
    for (int p=0;p<np;p++) {
      for (int x=0;x<n;x++) {
        uint64_t before=domains[x],kept=before&less_equal_mask[p];
        if (kept!=before) {
          uint64_t count=(uint64_t)__builtin_popcountll(before^kept);
          removals+=count;lex_removals+=count;domains[x]=kept;altered=1;
          if (!kept) return 0;
          changed(x);
        }
        if (domains[x]&~fixed_mask[p]) break;
      }
    }
    if (!altered) return 1;
  }
}

/* 0 = exhausted subtree, 1 = witness, 2 = limit. A limit propagates intact. */
static int visit(uint64_t *domains) {
  nodes++;
  if (nodes>node_limit || (double)(GetTickCount64()-started)/1000.0>seconds_limit) return 2;
  if (!propagate(domains)) return 0;
  int chosen=-1,best=DMAX+1;
  for (int x=0;x<n;x++) {
    int count=__builtin_popcountll(domains[x]);
    if (count>1 && (count<best || (count==best && degree[x]>degree[chosen]))) {
      chosen=x;best=count;
    }
  }
  if (chosen<0) {
    for (int x=0;x<n;x++) solution[x]=__builtin_ctzll(domains[x]);
    return 1;
  }
  uint64_t remaining=domains[chosen];
  while (remaining) {
    int value=__builtin_ctzll(remaining);remaining&=remaining-1;
    uint64_t child[NMAX];memcpy(child,domains,(size_t)n*sizeof(uint64_t));child[chosen]=BIT(value);
    int result=visit(child);if (result) return result;
  }
  return 0;
}

int main(void) {
  n=read_int();size=read_int();nc=read_int();ng=read_int();np=read_int();
  if (n<1 || n>NMAX || size<2 || size>DMAX || nc<0 || nc>n*(n-1)/2 || ng<0 || ng>GMAX || np<0 || np>PMAX) fail("Invalid model dimensions");
  if (scanf("%lf %" SCNu64,&seconds_limit,&node_limit)!=2 || seconds_limit<=0 || !node_limit) fail("Invalid budget");
  uint64_t allowed=size==64 ? UINT64_MAX : BIT(size)-1;
  for (int x=0;x<n;x++) { initial[x]=read_mask();if (initial[x]&~allowed) fail("Domain exceeds alphabet"); }
  for (int c=0;c<nc;c++) {
    int x=read_int(),y=read_int();
    if (x<0 || x>=n || y<0 || y>=n || x>=y || adjacent[x][y]) fail("Invalid relation pair");
    adjacent[x][y]=adjacent[y][x]=1;degree[x]++;degree[y]++;
    for (int u=0;u<size;u++) {
      uint64_t row=read_mask();if (row&~allowed) fail("Relation exceeds alphabet");relation[x][y][u]=row;
      while (row) { int v=__builtin_ctzll(row);row&=row-1;relation[y][x][v]|=BIT(u); }
    }
  }
  for (int g=0;g<ng;g++) for (int x=0;x<n;x++) {
    forbidden[g][x]=read_int();if (forbidden[g][x]<0 || forbidden[g][x]>=size) fail("Invalid forbidden value");
  }
  for (int p=0;p<np;p++) {
    uint64_t images=0;
    for (int u=0;u<size;u++) {
      int v=read_int();if (v<0 || v>=size || (images&BIT(v))) fail("Invalid permutation");images|=BIT(v);
      if (u==v) fixed_mask[p]|=BIT(u);
      if (u<=v) less_equal_mask[p]|=BIT(u);
    }
  }
  started=GetTickCount64();int result=visit(initial);
  printf("{\"status\":\"%s\",\"nodes\":%" PRIu64 ",\"removals\":%" PRIu64 ",\"lex_removals\":%" PRIu64 ",\"seconds\":%.3f,\"solution\":",
    result==0?"EXHAUSTED":result==1?"FOUND":"LIMIT",nodes,removals,lex_removals,(double)(GetTickCount64()-started)/1000.0);
  if (result==1) { putchar('[');for (int x=0;x<n;x++) printf("%s%d",x?",":"",solution[x]);putchar(']'); }
  else printf("null");
  puts("}");return 0;
}
