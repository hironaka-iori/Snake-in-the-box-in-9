"""Extend the saved support engine with checked-cardinality partner subsets."""
from pathlib import Path
H=Path(__file__).resolve().parents[1];P=H.parent/'212-spare-support'
assert not (H/'data/tight-compiler-receipt.json').exists()
def sub(s,a,b):
    assert s.count(a)==1,a[:80]
    return s.replace(a,b)
s=(P/'scripts/spare_solver.c').read_text()
s=sub(s,'static int propagate(uint64_t *domains) {',r'''
static uint64_t partner_match_calls,partner_subset_failures,partner_tight_sets,partner_tight_removals;

static int augment_partner(int row,const uint64_t *edges,int *owner,
    uint64_t *seen_columns,uint64_t *seen_rows) {
  *seen_rows|=BIT(row);
  uint64_t scan=edges[row];
  while (scan) {
    int col=__builtin_ctzll(scan);scan&=scan-1;
    if (*seen_columns&BIT(col)) continue;
    *seen_columns|=BIT(col);
    if (owner[col]<0 || augment_partner(owner[col],edges,owner,seen_columns,seen_rows)) {
      owner[col]=row;return 1;
    }
  }
  return 0;
}

/* Matching discovers candidate subsets. Every exclusion/deletion uses
   a recomputed neighbor set and its actual cardinality. */
static int tight_partners(SupportFamily *family,uint64_t *domains,int *altered) {
  int q=__builtin_popcountll(family->words),c=family->count,o=family->outside_count;
  if (q!=32 || c>32 || o>32) fail("Partner matcher requires the saved 32-word families");
  int spare=q-c,position[NMAX],owner[32];
  uint64_t real[32],edges[32],all=(BIT(32)-1),chosen=(BIT(c)-1),dummy=all&~chosen;
  for (int k=0;k<n;k++) position[k]=-1;
  for (int k=0;k<c;k++) position[family->clique[k]]=k;
  for (int k=0;k<32;k++) owner[k]=-1;
  partner_match_calls++;
  for (int k=0;k<o;k++) {
    real[k]=0;
    for (int j=0;j<family->partner_count[k];j++) {
      int y=family->partners[k][j],p=position[y];
      if (p<0) fail("Partner absent from chosen family");
      if (domains[family->outside[k]]&domains[y]) real[k]|=BIT(p);
    }
    edges[k]=real[k]|dummy;
  }
  for (int k=0;k<o;k++) {
    uint64_t seen_columns=0,seen_rows=0;
    if (!augment_partner(k,edges,owner,&seen_columns,&seen_rows)) {
      uint64_t neighbours=0,scan=seen_rows;
      while (scan) { int row=__builtin_ctzll(scan);scan&=scan-1;neighbours|=real[row]; }
      if (__builtin_popcountll(seen_rows)<=__builtin_popcountll(neighbours)+spare)
        fail("Matching failure has no deficient partner certificate");
      partner_subset_failures++;return 0;
    }
  }
  for (int start=0;start<o;start++) {
    uint64_t reached=BIT(start),pending_rows=reached,neighbours=0;
    int free_reached=0;
    while (pending_rows) {
      int row=__builtin_ctzll(pending_rows);pending_rows&=pending_rows-1;
      neighbours|=real[row];uint64_t cols=edges[row];
      while (cols) {
        int col=__builtin_ctzll(cols);cols&=cols-1;
        if (owner[col]<0) { free_reached=1;continue; }
        uint64_t bit=BIT(owner[col]);
        if (!(reached&bit)) { reached|=bit;pending_rows|=bit; }
      }
    }
    if (free_reached) continue;
    if (__builtin_popcountll(reached)!=__builtin_popcountll(neighbours)+spare)
      fail("Closed partner set is not tight");
    partner_tight_sets++;
    for (int k=0;k<o;k++) if (!(reached&BIT(k))) {
      int x=family->outside[k];uint64_t support=0;
      for (int j=0;j<family->partner_count[k];j++) {
        int y=family->partners[k][j];
        if (!(neighbours&BIT(position[y]))) support|=domains[y];
      }
      uint64_t before=domains[x],kept=before&support;
      if (kept!=before) {
        uint64_t removed=(uint64_t)__builtin_popcountll(before^kept);
        removals+=removed;partner_tight_removals+=removed;domains[x]=kept;*altered=1;
        if (!kept) { partner_subset_failures++;return 0; }
        changed(x);
      }
    }
  }
  return 1;
}

static int propagate(uint64_t *domains) {''')
s=sub(s,'    if (!altered) return 1;', '''    for (int f=0;f<family_count;f++)
      if (!tight_partners(&families[f],domains,&altered)) return 0;
    if (!altered) return 1;''')
s=sub(s,'support_calls,support_removals,support_failures,saturated_budgets);return 0;',
      'support_calls,support_removals,support_failures,saturated_budgets);return 0;')
# Extend the existing final JSON without changing any earlier counters.
s=sub(s,r'\"saturated_budgets\":%" PRIu64 "}\n",',
      r'\"saturated_budgets\":%" PRIu64 ",\"partner_match_calls\":%" PRIu64 ",\"partner_subset_failures\":%" PRIu64 ",\"partner_tight_sets\":%" PRIu64 ",\"partner_tight_removals\":%" PRIu64 "}\n",')
s=sub(s,'support_calls,support_removals,support_failures,saturated_budgets);return 0;',
      'support_calls,support_removals,support_failures,saturated_budgets,partner_match_calls,partner_subset_failures,partner_tight_sets,partner_tight_removals);return 0;')
(H/'scripts/tight_solver.c').write_text(s,encoding='utf-8',newline='\n')
for src,dst in [('spare_continue.py','tight_continue.py'),('compile_spare.py','compile_tight.py')]:
    s=(P/'scripts'/src).read_text().replace('spare_solver','tight_solver').replace('spare-batch-','tight-batch-').replace('spare-search-progress','tight-search-progress').replace('spare-compiler','tight-compiler')
    (H/'scripts'/dst).write_text(s,encoding='utf-8',newline='\n')
for name in ['history_model.py']:(H/'scripts'/name).write_bytes((P/'scripts'/name).read_bytes())
for name in ['lower-dimensional-input.json','square-capacity.json']:(H/'data'/name).write_bytes((P/'data'/name).read_bytes())
print('PREPARED_TIGHT_PARTNER_ENGINE')
