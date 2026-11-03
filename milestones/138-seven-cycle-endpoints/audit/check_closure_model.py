"""Check the native SAT assignment for the sole-extra-cycle experiment."""
from pathlib import Path
import hashlib, itertools, json
H=Path(__file__).resolve().parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
w=H/'work/certificate-closure'
native=json.loads((H/'data/native-closure.json').read_text())
assert native['status']=='NATIVE_NON_UNSAT' and native['exit_code']==10
out=(w/'stdout.txt').read_text();assert 's SATISFIABLE' in out
lits=[int(x) for row in out.splitlines() if row.startswith('v ') for x in row.split()[1:] if x!='0']
a={abs(x):x>0 for x in lits};assert len(a)==len(lits)
rows=(w/'input.cnf').read_text().splitlines();_,_,nv,nc=rows[0].split()
assert set(a)==set(range(1,int(nv)+1))
clauses=[[int(x) for x in row.split()[:-1]] for row in rows[1:]]
assert len(clauses)==int(nc)
assert all(any(a[abs(x)]==(x>0) for x in c) for c in clauses)
selected={v for v in range(512) if a[v+1]}
neighbors={v:{u for u in selected if (u^v).bit_count()==1} for v in selected}
assert all(1<=len(ns)<=2 for ns in neighbors.values())
assert sum(len(ns)==1 for ns in neighbors.values())<=2
remaining=set(selected);components=[]
while remaining:
 todo=[min(remaining)];component=set()
 while todo:
  v=todo.pop()
  if v in component:continue
  component.add(v);todo.extend(neighbors[v]-component)
 remaining-=component
 components.append(dict(vertices=sorted(component),size=len(component),cycle=all(len(neighbors[v])==2 for v in component)))
meta=json.loads((H/'work/closure/encoding.json').read_text())
window=meta['window'];counts=[]
assert set(window)<=selected
for i,c in enumerate(window[1:-1],1):
 used={((c^window[j]).bit_length()-1) for j in [i-1,i+1]}
 corners=[c^(1<<d)^(1<<e) for d,e in itertools.combinations([d for d in range(9) if d not in used],2)]
 assert len(corners)==21
 count=sum(v not in selected for v in corners);counts.append(count)
 assert meta['bounds'][i-1][0]<=count<=meta['bounds'][i-1][1]
assert any(c['cycle'] for c in components)
record=dict(status='PASS_NATIVE_SAT_MODEL_CHECK',variables=int(nv),clauses_checked=len(clauses),selected_vertices=len(selected),counts=counts,components=components,actual_snake=False,input_sha256=sha(w/'input.cnf'),stdout_sha256=sha(w/'stdout.txt'),script_sha256=sha(Path(__file__)),scope='Satisfying assignment of the full degree/count relaxation with one extra cycle excluded. It contains a cycle and is not an actual snake; this only disproves sufficiency of that single extra cut.')
(H/'data/closure-model-review.json').write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:v for k,v in record.items() if k!='components'}))
