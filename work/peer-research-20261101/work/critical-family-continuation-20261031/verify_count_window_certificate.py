"""Read the standalone DIMACS/LRAT afresh, reconstruct source rows, and replay.
Does not invoke the producer or CDCL. Ordinary mathematical proof checker,
not Lean kernel verification.
"""
from pathlib import Path
import json,hashlib,sys,collections
H=Path(__file__).resolve().parent;O=H/'count_window_certificate';M=json.loads((O/'manifest.json').read_text())
for name,digest in M['files_sha256'].items():assert hashlib.sha256((O/name).read_bytes()).hexdigest()==digest
clauses=[]
for line in (O/'core.cnf').read_text().splitlines():
 if line.startswith('p '):_,_,nv,nc=line.split();nv=int(nv);nc=int(nc)
 elif line and not line.startswith('c'):
  a=list(map(int,line.split()));assert a[-1]==0 and all(1<=abs(l)<=nv for l in a[:-1]);clauses.append(a[:-1])
assert len(clauses)==nc;db=[tuple(c) for c in clauses];hints=0;steps=0;last=None
for line in (O/'proof.lrat').read_text().splitlines():
 a=list(map(int,line.split()));assert a[0]==len(db)+1 and a[-1]==0;split=a.index(0,1);cl=a[1:split];ids=a[split+1:-1];values={abs(l):l<0 for l in cl};assert len(values)==len({abs(l) for l in cl});conflict=False
 for position,cid in enumerate(ids):
  assert 1<=cid<=len(db);C=db[cid-1];assert not any(abs(l) in values and values[abs(l)]==(l>0) for l in C)
  unknown={l for l in C if abs(l) not in values}
  if not unknown:assert position==len(ids)-1;conflict=True
  else:assert len(unknown)==1;l=next(iter(unknown));values[abs(l)]=l>0
  hints+=1
 assert conflict;db.append(tuple(cl));last=cl;steps+=1
assert last==[] and steps==353 and hints==30020
sys.path.insert(0,str(H));from zero_share_probe import build
records={e['source_edge']:e for e in json.loads((H/'filtered_critical_edges.json').read_text())};E,meta=build(records[1657683]);assert meta['source_wincert_sha256']==M['source_wincert_sha256'];vmap=M['variable_mapping_new_to_source'];rows=M['original_clause_indices'];core_mapped=[[vmap[abs(l)-1]*(1 if l>0 else -1) for l in c] for c in clauses];assert core_mapped==[E.clauses[i-1] for i in rows]
allowed={'alpha<=3@7','alpha>=3@7','alpha<=5@15','alpha<=3@13','alpha<=5@28'};source_inverse={x:v for v,x in E.var.items()};cycle_clauses=0
for row,c in zip(rows,core_mapped):
 kind=E.kinds[row-1]
 if kind.startswith('alpha'):assert kind in allowed
 if kind in ['no4cycle','no6cycle']:
  assert all(l<0 and -l in source_inverse for l in c);V={source_inverse[-l] for l in c};assert len(V)==len(c) and all(sum((a^b).bit_count()==1 for b in V)==2 for a in V)
  reached={next(iter(V))};todo=list(reached)
  while todo:
   for w in V-reached:
    if (todo[-1]^w).bit_count()==1:reached.add(w);todo.append(w);break
   else:todo.pop()
  assert reached==V;cycle_clauses+=1
r={'status':'PASS_FRESH_DIMACS_LRAT_AND_SOURCE_REBUILD','variables':nv,'clauses':nc,'RUP_steps':steps,'hints':hints,'source_rows_exactly_reconstructed':True,'all_alpha_rows_within_declared_four_count_hypotheses':True,'actual_cube_cycle_clauses_checked':cycle_clauses,'share_or_objective_premise_used':False,'new_global_bound':None,'Lean_checked':False}
(O/'independent_verification.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))
