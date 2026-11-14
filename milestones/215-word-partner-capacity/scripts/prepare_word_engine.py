"""Combine finite word-union capacity with the accepted partner rule."""
from pathlib import Path
H=Path(__file__).resolve().parents[1];P=H.parent/'214-parity-partner-capacity'
assert not (H/'data/word-compiler-receipt.json').exists()
def sub(s,a,b):
    assert s.count(a)==1,a[:100]
    return s.replace(a,b)
s=(P/'scripts/tight_solver.c').read_text()
s=sub(s,'static int propagate(uint64_t *domains) {',r'''
static uint64_t word_match_calls,word_subset_failures,word_tight_sets,word_subset_removals;

/* Each family has pairwise distinct assigned words. Matching only finds
   subsets; explicit domain-union cardinalities justify every deduction. */
static int distinct_words(const int *ids,int count,uint64_t *domains,int *altered) {
  if (count<0 || count>32) fail("Saved word family exceeds 32 intervals");
  int owner[64];uint64_t edges[32];
  for (int w=0;w<64;w++) owner[w]=-1;
  for (int j=0;j<count;j++) edges[j]=domains[ids[j]];
  word_match_calls++;
  for (int j=0;j<count;j++) {
    uint64_t seen_columns=0,seen_rows=0;
    if (!augment_partner(j,edges,owner,&seen_columns,&seen_rows)) {
      uint64_t words=0,scan=seen_rows;
      while (scan) { int row=__builtin_ctzll(scan);scan&=scan-1;words|=domains[ids[row]]; }
      if (__builtin_popcountll(words)>=__builtin_popcountll(seen_rows))
        fail("Word matching failure has no deficient union certificate");
      word_subset_failures++;return 0;
    }
  }
  for (int start=0;start<count;start++) {
    uint64_t reached=BIT(start),pending_rows=reached,old_words=0;
    int free_reached=0;
    while (pending_rows) {
      int row=__builtin_ctzll(pending_rows);pending_rows&=pending_rows-1;
      old_words|=edges[row];uint64_t scan=edges[row];
      while (scan) {
        int w=__builtin_ctzll(scan);scan&=scan-1;
        if (owner[w]<0) { free_reached=1;continue; }
        uint64_t bit=BIT(owner[w]);
        if (!(reached&bit)) { reached|=bit;pending_rows|=bit; }
      }
    }
    if (free_reached) continue;
    if (__builtin_popcountll(old_words)!=__builtin_popcountll(reached))
      fail("Closed word set is not tight");
    /* Earlier deletions can shrink these domains. Recompute the union
       and reject a genuine deficiency before applying saturation. */
    uint64_t words=0,scan=reached;
    while (scan) { int row=__builtin_ctzll(scan);scan&=scan-1;words|=domains[ids[row]]; }
    int used=__builtin_popcountll(words),needed=__builtin_popcountll(reached);
    if (used<needed) { word_subset_failures++;return 0; }
    if (used!=needed) fail("Word union grew during propagation");
    word_tight_sets++;
    for (int j=0;j<count;j++) if (!(reached&BIT(j))) {
      int x=ids[j];uint64_t before=domains[x],kept=before&~words;
      if (kept!=before) {
        uint64_t removed=(uint64_t)__builtin_popcountll(before^kept);
        domains[x]=kept;removals+=removed;word_subset_removals+=removed;*altered=1;
        if (!kept) { word_subset_failures++;return 0; }
        changed(x);
      }
    }
  }
  return 1;
}

static int propagate(uint64_t *domains) {''')
s=sub(s,'    for (int f=0;f<family_count;f++)\n      if (!tight_partners(&families[f],domains,&altered)) return 0;', '''    for (int f=0;f<family_count;f++) {
      SupportFamily *family=&families[f];
      if (!distinct_words(family->clique,family->count,domains,&altered)) return 0;
      if (!distinct_words(family->outside,family->outside_count,domains,&altered)) return 0;
    }
    for (int f=0;f<family_count;f++)
      if (!tight_partners(&families[f],domains,&altered)) return 0;''')
s=sub(s,r'\"partner_tight_removals\":%" PRIu64 "}\n",',
      r'\"partner_tight_removals\":%" PRIu64 ",\"word_match_calls\":%" PRIu64 ",\"word_subset_failures\":%" PRIu64 ",\"word_tight_sets\":%" PRIu64 ",\"word_subset_removals\":%" PRIu64 "}\n",')
s=sub(s,'partner_match_calls,partner_subset_failures,partner_tight_sets,partner_tight_removals);return 0;',
      'partner_match_calls,partner_subset_failures,partner_tight_sets,partner_tight_removals,word_match_calls,word_subset_failures,word_tight_sets,word_subset_removals);return 0;')
(H/'scripts/word_solver.c').write_text(s,encoding='utf-8',newline='\n')
for src,dst in [('tight_continue.py','word_continue.py'),('compile_tight.py','compile_word.py')]:
    s=(P/'scripts'/src).read_text().replace('tight_solver','word_solver').replace('tight-batch-','word-batch-').replace('tight-search-progress','word-search-progress').replace('tight-compiler','word-compiler')
    (H/'scripts'/dst).write_text(s,encoding='utf-8',newline='\n')
(H/'scripts/history_model.py').write_bytes((P/'scripts/history_model.py').read_bytes())
for name in ['lower-dimensional-input.json','square-capacity.json']:(H/'data'/name).write_bytes((P/'data'/name).read_bytes())
print('PREPARED_WORD_AND_PARTNER_ENGINE')
