"""Build a separate subset-capacity engine, preserving frozen evidence."""
from pathlib import Path
H=Path(__file__).resolve().parents[1]
P=H.parent/'209-slice-capacity'
def sub(s,a,b):
    if s.count(a)!=1:raise RuntimeError('Nonunique replacement: '+a[:80])
    return s.replace(a,b)
c=(P/'scripts/capacity_solver.c').read_text()
c=sub(c,'static uint64_t cap_words, capacity_removals, partner_removals, capacity_failures;',
'''static uint64_t cap_words, capacity_removals, partner_removals, capacity_failures;
static uint64_t subset_calls, subset_removals, subset_failures, tight_sets;''')
new=r'''/* Matching discovers subsets; explicit union cardinalities justify pruning. */
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

static int propagate(uint64_t *domains) {'''
c=sub(c,'static int propagate(uint64_t *domains) {',new)
c=sub(c,'    if (!altered) return 1;','    if (!subset_propagate(domains,&altered)) return 0;\n    if (!altered) return 1;')
c=sub(c,'cap_count<1 || cap_count>NMAX','cap_count<1 || cap_count>DMAX')
c=sub(c,'    capacity_removals,partner_removals,capacity_failures);return 0;',
    '    capacity_removals,partner_removals,capacity_failures,subset_calls,subset_removals,subset_failures,tight_sets);return 0;')
c=sub(c,r'''\"capacity_failures\":%" PRIu64 "}\n",''',r'''\"capacity_failures\":%" PRIu64 ",\"subset_calls\":%" PRIu64 ",\"subset_removals\":%" PRIu64 ",\"subset_failures\":%" PRIu64 ",\"tight_sets\":%" PRIu64 "}\n",''')
(H/'scripts/capacity_solver.c').write_text(c,encoding='utf-8',newline='\n')
p=(P/'scripts/capacity_continue.py').read_text().replace(
    '"""Saturated-clique continuation; no Lean search certificate."""',
    '"""Subset-capacity continuation from an explicit transferred frontier; native evidence."""')
a=p.index(' folder.mkdir()\n');b=p.index('\ndef one_job(',a)
p=p[:a]+" raise RuntimeError('Create the explicit transfer record before continuation.')\n"+p[b:]
(H/'scripts/capacity_continue.py').write_text(p,encoding='utf-8',newline='\n')
print('Prepared separate subset engine and continuation runner.')
