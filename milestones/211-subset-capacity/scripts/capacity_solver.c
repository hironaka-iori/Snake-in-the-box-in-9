/* Exact residual-symmetry search with saved unfinished domains.
   A result applies to its input domain vector, not automatically the full model.
   This program supplies no Lean certificate. */
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
__declspec(dllimport) unsigned long __stdcall GetFileAttributesA(const char *);
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
static uint64_t pending[NMAX+1][NMAX];
static int pending_count;
static int cap_count, cap_vars[NMAX], cover_count;
static int cover_x[NMAX], cover_n[NMAX], cover_partner[NMAX][NMAX];
static uint64_t cap_words, capacity_removals, partner_removals, capacity_failures;
static uint64_t subset_calls, subset_removals, subset_failures, tight_sets;

static void save_pending(const uint64_t *domains) {
  if (pending_count>=NMAX+1) { puts("Pending-domain capacity exceeded"); exit(3); }
  memcpy(pending[pending_count++],domains,(size_t)n*sizeof(uint64_t));
}

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
/* Matching discovers subsets; explicit union cardinalities justify pruning. */
static int augment(int x, const uint64_t *domains, int *owner,
                   uint64_t *seen_words, uint64_t *seen_vars) {
  if (*seen_vars & BIT(x)) return 0;
  *seen_vars |= BIT(x);
  uint64_t scan=domains[cap_vars[x]];
  while (scan) {
    int u=__builtin_ctzll(scan); scan&=scan-1;
    if (*seen_words & BIT(u)) continue;
    *seen_words |= BIT(u);
    if (owner[u]<0 || augment(owner[u],domains,owner,seen_words,seen_vars)) {
      owner[u]=x; return 1;
    }
  }
  return 0;
}
static uint64_t subset_union(uint64_t members, const uint64_t *domains) {
  uint64_t words=0;
  while (members) {
    int k=__builtin_ctzll(members);members&=members-1;
    words|=domains[cap_vars[k]];
  }
  return words;
}
static int subset_propagate(uint64_t *domains, int *altered) {
  subset_calls++;
  int owner[DMAX];
  for (int u=0;u<DMAX;u++) owner[u]=-1;
  for (int k=0;k<cap_count;k++) {
    uint64_t seen_words=0,seen_vars=0;
    if (!augment(k,domains,owner,&seen_words,&seen_vars)) {
      uint64_t available=subset_union(seen_vars,domains);
      if (__builtin_popcountll(available)>=__builtin_popcountll(seen_vars))
        fail("Failed matching lacks a deficient subset witness");
      subset_failures++;return 0;
    }
  }
  uint64_t matched=0;
  for (int u=0;u<size;u++) if (owner[u]>=0) {
    int k=owner[u];
    if (k>=cap_count || (matched&BIT(k)) || !(domains[cap_vars[k]]&BIT(u)))
      fail("Invalid matching witness");
    matched|=BIT(k);
  }
  if (__builtin_popcountll(matched)!=cap_count) fail("Incomplete matching witness");
  uint64_t reach[DMAX];
  for (int k=0;k<cap_count;k++) {
    reach[k]=BIT(k);
    uint64_t scan=domains[cap_vars[k]];
    while (scan) {
      int u=__builtin_ctzll(scan);scan&=scan-1;
      if (owner[u]<0) fail("Unmatched word in saturated alphabet");
      reach[k]|=BIT(owner[u]);
    }
  }
  for (int k=0;k<cap_count;k++)
    for (int j=0;j<cap_count;j++)
      if (reach[j]&BIT(k)) reach[j]|=reach[k];
  for (int k=0;k<cap_count;k++) {
    uint64_t members=reach[k],available=subset_union(members,domains);
    int count=__builtin_popcountll(members),width=__builtin_popcountll(available);
    if (width<count) { subset_failures++;return 0; }
    if (width!=count || count==cap_count) continue;
    tight_sets++;
    /* Only other members of the declared all-different family are pruned. */
    for (int j=0;j<cap_count;j++) if (!(members&BIT(j))) {
      int x=cap_vars[j];uint64_t before=domains[x],kept=before&~available;
      if (before!=kept) {
        uint64_t removed=(uint64_t)__builtin_popcountll(before^kept);
        domains[x]=kept;removals+=removed;subset_removals+=removed;
        *altered=1;
        if (!kept) { subset_failures++;return 0; }
        changed(x);
      }
    }
  }
  return 1;
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
    /* The declared distinct-word clique takes every declared word once. */
    uint64_t words=cap_words;
    while (words) {
      int u=__builtin_ctzll(words); words&=words-1;
      int count=0, carrier=-1;
      for (int k=0;k<cap_count;k++) if (domains[cap_vars[k]]&BIT(u)) {
        count++; carrier=cap_vars[k];
      }
      if (!count) { capacity_failures++; return 0; }
      if (count==1 && domains[carrier]!=BIT(u)) {
        uint64_t removed=(uint64_t)__builtin_popcountll(domains[carrier])-1;
        removals+=removed; capacity_removals+=removed;
        domains[carrier]=BIT(u); altered=1; changed(carrier);
      }
    }
    for (int k=0;k<cover_count;k++) {
      uint64_t available=0;
      for (int j=0;j<cover_n[k];j++) available|=domains[cover_partner[k][j]];
      int x=cover_x[k]; uint64_t before=domains[x], kept=before&available;
      if (kept!=before) {
        uint64_t removed=(uint64_t)__builtin_popcountll(before^kept);
        removals+=removed; partner_removals+=removed;
        domains[x]=kept; altered=1;
        if (!kept) { capacity_failures++; return 0; }
        changed(x);
      }
    }
    if (!subset_propagate(domains,&altered)) return 0;
    if (!altered) return 1;
  }
}

/* 0 = exhausted subtree, 1 = witness, 2 = covered by saved pending domains. */
static int visit(uint64_t *domains) {
  nodes++;
  if (nodes>node_limit || (double)(GetTickCount64()-started)/1000.0>seconds_limit ||
      ((nodes&255)==1 && GetFileAttributesA("STOP")!=0xffffffffUL)) {
    save_pending(domains);return 2;
  }
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
    int result=visit(child);
    if (result==1) return 1;
    if (result==2) {
      if (remaining) {
        uint64_t unvisited[NMAX];memcpy(unvisited,domains,(size_t)n*sizeof(uint64_t));
        unvisited[chosen]=remaining;save_pending(unvisited);
      }
      return 2;
    }
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
  cap_count=read_int();cap_words=read_mask();cover_count=read_int();
  if (cap_count<1 || cap_count>DMAX || cap_count!=__builtin_popcountll(cap_words)
      || (cap_words&~allowed) || cover_count<0 || cover_count>NMAX) fail("Invalid capacity header");
  unsigned char cap_seen[NMAX]={0}, cover_seen[NMAX]={0};
  for (int k=0;k<cap_count;k++) {
    int x=read_int();
    if (x<0 || x>=n || cap_seen[x] || (initial[x]&~cap_words)) fail("Invalid capacity variable");
    cap_seen[x]=1;cap_vars[k]=x;
  }
  for (int k=0;k<cover_count;k++) {
    int x=read_int(), count=read_int();
    if (x<0 || x>=n || cap_seen[x] || cover_seen[x] || count<1 || count>cap_count
        || (initial[x]&~cap_words)) fail("Invalid covered variable");
    cover_seen[x]=1;cover_x[k]=x;cover_n[k]=count;
    unsigned char partners[NMAX]={0};
    for (int j=0;j<count;j++) {
      int y=read_int();
      if (y<0 || y>=n || !cap_seen[y] || partners[y]) fail("Invalid capacity partner");
      partners[y]=1;cover_partner[k][j]=y;
    }
  }
  started=GetTickCount64();int result=visit(initial);
  printf("{\"status\":\"%s\",\"nodes\":%" PRIu64 ",\"removals\":%" PRIu64 ",\"lex_removals\":%" PRIu64 ",\"seconds\":%.3f,\"solution\":",
    result==0?"EXHAUSTED":result==1?"FOUND":"LIMIT",nodes,removals,lex_removals,(double)(GetTickCount64()-started)/1000.0);
  if (result==1) { putchar('[');for (int x=0;x<n;x++) printf("%s%d",x?",":"",solution[x]);putchar(']'); }
  else printf("null");
  printf(",\"pending\":[");
  for (int job=0;job<pending_count;job++) {
    printf("%s[",job?",":"");
    for (int x=0;x<n;x++) printf("%s%" PRIu64,x?",":"",pending[job][x]);
    putchar(']');
  }
  printf("],\"capacity_removals\":%" PRIu64 ",\"partner_removals\":%" PRIu64 ",\"capacity_failures\":%" PRIu64 ",\"subset_calls\":%" PRIu64 ",\"subset_removals\":%" PRIu64 ",\"subset_failures\":%" PRIu64 ",\"tight_sets\":%" PRIu64 "}\n",
    capacity_removals,partner_removals,capacity_failures,subset_calls,subset_removals,subset_failures,tight_sets);return 0;
}
