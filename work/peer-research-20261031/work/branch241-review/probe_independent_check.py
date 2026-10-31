"""Independent review of the actual-window probe artifacts."""
import gzip,json,hashlib
from pathlib import Path
from independent_encoding_review import direct,Geometry
from rup_check import check
ROOT=Path(__file__).parent;rows=[]
for p in sorted((ROOT/'probes').glob('*.json.gz')):
 d=json.loads(gzip.decompress(p.read_bytes()));r=d['result'];row={'artifact':p.name,'status':r['status']}
 row['RUP']=check(d['clauses'],d['proof'],require_empty=r['status']=='UNSAT')
 if r['status']=='SAT':
  S=set(r['selection']);adj={x:[y for y in S if (x^y).bit_count()==1] for x in S};seen=set();comps=[]
  for x in S:
   if x in seen:continue
   stack=[x];seen.add(x);comp=[]
   while stack:
    v=stack.pop();comp.append(v)
    for w in adj[v]:
     if w not in seen:seen.add(w);stack.append(w)
   comps.append({'vertices':len(comp),'cycle':all(len(adj[v])==2 for v in comp)})
  vals=[direct(Geometry(9),S,x) for x in d['meta']['path'][1:-1]]
  cost=sum(21*a+2*b+c+v for a,b,c,v,exact in vals)
  assert cost<=d['meta']['cap_scaled21'];assert all(len(ns)<=2 for ns in adj.values())
  row.update(selected_vertices=len(S),independent_cost_scaled21=cost,cycle_sizes=sorted([c['vertices'] for c in comps if c['cycle']]),noncycle_component_sizes=sorted([c['vertices'] for c in comps if not c['cycle']]))
 rows.append(row)
(ROOT/'probe_independent_results.json').write_text(json.dumps(rows,indent=2));print(json.dumps(rows,indent=2))
