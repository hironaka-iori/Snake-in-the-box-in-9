"""Create a separate engine using consequences of a saturated slice clique."""
from pathlib import Path
H=Path(__file__).resolve().parents[1]

def sub(text,old,new):
    if text.count(old)!=1: raise RuntimeError(old[:80])
    return text.replace(old,new)

c=(H/'scripts/history_solver.c').read_text()
c=sub(c,'static int pending_count;','''static int pending_count;
static int cap_count, cap_vars[NMAX], cover_count;
static int cover_x[NMAX], cover_n[NMAX], cover_partner[NMAX][NMAX];
static uint64_t cap_words, capacity_removals, partner_removals, capacity_failures;''')
c=sub(c,'    if (!altered) return 1;','''    /* The declared distinct-word clique takes every declared word once. */
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
    if (!altered) return 1;''')
c=sub(c,'  started=GetTickCount64();int result=visit(initial);','''  cap_count=read_int();cap_words=read_mask();cover_count=read_int();
  if (cap_count<1 || cap_count>NMAX || cap_count!=__builtin_popcountll(cap_words)
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
  started=GetTickCount64();int result=visit(initial);''')
c=sub(c,'  puts("]}");return 0;',r'''  printf("],\"capacity_removals\":%" PRIu64 ",\"partner_removals\":%" PRIu64 ",\"capacity_failures\":%" PRIu64 "}\n",
    capacity_removals,partner_removals,capacity_failures);return 0;''')
(H/'scripts/capacity_solver.c').write_text(c,encoding='utf-8')

p=(H/'scripts/continue_search.py').read_text()
p=p.replace('scripts/history_solver.c','scripts/capacity_solver.c').replace('build/history_solver.exe','build/capacity_solver.exe')
p=sub(p,"H/'data/lower-dimensional-input.json']}","H/'data/lower-dimensional-input.json',H/'data/square-capacity.json']}")
p=sub(p,"m=json.loads((folder/'model.json').read_bytes());perms=json.loads((folder/'permutations.json').read_bytes())\n assert len(m['block'])==6 and len(perms)==120",'''m=json.loads((folder/'model.json').read_bytes());perms=json.loads((folder/'permutations.json').read_bytes())
 assert index==23 and len(m['block'])==6 and len(perms)==120
 census=json.loads((H/'data/square-capacity.json').read_bytes())
 record=next(r for r in census['records'] if r['index']==index)
 assert record['model_sha256']==sha(folder/'model.json')
 part=record['parities'][0];clique=part['clique'];partners=part['opposite_singleton_partners']
 words=sum(1<<u for u in range(64) if u.bit_count()%2==0)
 assert part['saturated'] and len(clique)==32 and len(set(clique))==32
 assert all(g%2==0 and m['domains'][g]&~words==0 for g in clique)
 table={(c['x'],c['y']):c['rows'] for c in m['constraints']}
 def unequal(x,y):
  rows=table.get(tuple(sorted([x,y])))
  return rows is not None and all(not(rows[u]>>u&1) for u in range(64) if words>>u&1)
 assert all(unequal(x,y) for k,x in enumerate(clique) for y in clique[k+1:])
 assert set(map(int,partners))==set(part['outside'])
 for raw,ys in partners.items():
  x=int(raw)
  assert x not in clique and x%2==0 and ys and len(set(ys))==len(ys) and set(ys)<=set(clique)
  assert m['domains'][x]&~words==0
  assert all(unequal(x,y) for y in clique if y not in ys)
 capacity={'clique':clique,'words':words,'partners':partners,'model_sha256':sha(folder/'model.json'),
  'scope':'Equal-size distinct-word clique covers all even words; outside equality can occur only with listed partners.'}
 save(folder/'capacity-constraints.json',capacity)''')
p=sub(p,"tail+=[' '.join(map(str,v)) for v in m['nogoods']]+[' '.join(map(str,p)) for p in perms]",'''tail+=[' '.join(map(str,v)) for v in m['nogoods']]+[' '.join(map(str,p)) for p in perms]
 tail += [f'{len(clique)} {words} {len(partners)}',' '.join(map(str,clique))]
 tail += [' '.join(map(str,[int(x),len(ys),*ys])) for x,ys in partners.items()]''')
p=sub(p,"['model.json','permutations.json','input-tail.txt']","['model.json','permutations.json','input-tail.txt','capacity-constraints.json']")
p=sub(p,'default=[18]','default=[23]')
p=sub(p,'all(0<=i<28 for i in a.indices)','all(i==23 for i in a.indices)')
p=sub(p,"'batch-'+str(time.time_ns())","'capacity-batch-'+str(time.time_ns())")
p=sub(p,"H/'data/search-progress.json'","H/'data/capacity-search-progress.json'")
p=sub(p,'"""Durable native finite-domain continuation; no Lean search certificate."""','"""Saturated-clique continuation; no Lean search certificate."""')
(H/'scripts/capacity_continue.py').write_text(p,encoding='utf-8')
print('Prepared separate capacity source and runner; existing pinned engine unchanged.')
