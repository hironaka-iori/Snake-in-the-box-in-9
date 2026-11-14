from pathlib import Path
H=Path(__file__).resolve().parents[1]
P=H.parent/'215-word-partner-capacity'
s=(P/'scripts/word_solver.c').read_text(encoding='utf-8')
helper=r'''
static uint64_t joint_pair_removals,joint_triples,joint_sweeps,joint_new_relations;

static uint64_t pair_row(int x,int y,int u) {
  return adjacent[x][y] ? relation[x][y][u] : (size==64 ? UINT64_MAX : BIT(size)-1);
}

/* Delete only pairs in the submitted root domains. Both orientations are
   updated together. Missing relations mean the universal relation. */
static void restrict_pair(int x,int y,const uint64_t *domains,const uint64_t *kept) {
  uint64_t scan=domains[x];
  while (scan) {
    int u=__builtin_ctzll(scan);scan&=scan-1;
    uint64_t removed=pair_row(x,y,u)&domains[y]&~kept[u];
    if (!removed) continue;
    if (!adjacent[x][y]) {
      uint64_t allowed=size==64 ? UINT64_MAX : BIT(size)-1;
      for (int w=0;w<size;w++) relation[x][y][w]=relation[y][x][w]=allowed;
      adjacent[x][y]=adjacent[y][x]=1;degree[x]++;degree[y]++;
      joint_new_relations++;
    }
    relation[x][y][u]&=~removed;
    joint_pair_removals+=(uint64_t)__builtin_popcountll(removed);
    while (removed) {
      int v=__builtin_ctzll(removed);removed&=removed-1;
      relation[y][x][v]&=~BIT(u);
    }
  }
}

/* These tables are strengthened only at the root of one submitted job.
   Every descendant has smaller domains, and every new job reloads the
   original input relations. No branch-local restriction can leak back. */
static int project_root_pairs(const uint64_t *domains) {
  uint64_t before=joint_pair_removals;
  joint_sweeps++;
  for (int a=0;a+2<n;a++) {
    int b=a+1,c=a+2;
    uint64_t ab[DMAX]={0},bc[DMAX]={0},ac[DMAX]={0};
    uint64_t left=domains[a];
    joint_triples++;
    while (left) {
      int u=__builtin_ctzll(left);left&=left-1;
      uint64_t middle=pair_row(a,b,u)&domains[b];
      while (middle) {
        int v=__builtin_ctzll(middle);middle&=middle-1;
        uint64_t right=pair_row(b,c,v)&pair_row(a,c,u)&domains[c];
        if (right) { ab[u]|=BIT(v);bc[v]|=right;ac[u]|=right; }
      }
    }
    restrict_pair(a,b,domains,ab);
    restrict_pair(b,c,domains,bc);
    restrict_pair(a,c,domains,ac);
  }
  return joint_pair_removals!=before;
}

'''
anchor='static int propagate(uint64_t *domains) {'
assert s.count(anchor)==1
s=s.replace(anchor,helper+anchor,1)
anchor='  if (!propagate(domains)) return 0;\n  int chosen=-1,best=DMAX+1;'
assert s.count(anchor)==1
s=s.replace(anchor,'''  if (!propagate(domains)) return 0;
  if (nodes==1) {
    for (int pass=0;pass<4;pass++) {
      if (!project_root_pairs(domains)) break;
      if (!propagate(domains)) return 0;
    }
  }
  int chosen=-1,best=DMAX+1;''',1)
old=r'''",\"word_subset_removals\":%" PRIu64 "}\n",'''
new=r'''",\"word_subset_removals\":%" PRIu64 ",\"joint_pair_removals\":%" PRIu64 ",\"joint_triples\":%" PRIu64 ",\"joint_sweeps\":%" PRIu64 ",\"joint_new_relations\":%" PRIu64 "}\n",'''
assert s.count(old)==1
s=s.replace(old,new,1)
old='word_tight_sets,word_subset_removals);return 0;'
assert s.count(old)==1
s=s.replace(old,'word_tight_sets,word_subset_removals,joint_pair_removals,joint_triples,joint_sweeps,joint_new_relations);return 0;',1)
(H/'scripts/joint_solver.c').write_text(s,encoding='utf-8',newline='\n')
for name in ['history_model.py','native_resources.py']:
    (H/'scripts'/name).write_bytes((P/'scripts'/name).read_bytes())
for name in ['lower-dimensional-input.json','square-capacity.json']:
    (H/'data'/name).write_bytes((P/'data'/name).read_bytes())
for old,new in [('word_continue.py','joint_continue.py'),('compile_word.py','compile_joint.py')]:
    text=(P/'scripts'/old).read_text(encoding='utf-8').replace('word_solver','joint_solver').replace('word-batch','joint-batch').replace('word-search-progress','joint-search-progress').replace('word-compiler','joint-compiler')
    (H/'scripts'/new).write_text(text,encoding='utf-8',newline='\n')
print('PREPARED_JOINT_ENGINE')
