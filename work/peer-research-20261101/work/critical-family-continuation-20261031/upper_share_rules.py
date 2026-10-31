from pathlib import Path
import json,sys,collections,gzip
H=Path(__file__).resolve().parent;sys.path.insert(0,str(H));from zero_share_probe import build
sys.path.insert(0,str(H.parent/'branch241-review'));from solver import Solver
from rup_check import check

def pack(edge,lower_zero=False):
 edge=dict(edge)
 if lower_zero:edge['count_bounds']=[(0,c) if c<6 else (0,21) for c in edge['counts']]
 E,m=build(edge);base=E.clauses[:m['base_clauses']];faces=E.clauses[m['base_clauses']:];inverse={x:v for v,x in E.var.items()};w=[]
 for F in faces:w.append(sum(any((c^inverse[q]).bit_count()==1 for q in F) for c in m['charged_centres']))
 active=list(range(len(faces)));groups=[];proofs=[];total=0
 for _ in range(100):
  cs=base+[faces[i] for i in active];solver=Solver(cs,E.nv)
  if solver.root_conflict is None:break
  r=solver.solve(0);assert r['status']=='UNSAT';check(cs,solver.proof);used=sorted({active[h-len(base)-1] for p in solver.proof for h in p['hints'] if h>len(base)})
  if not used:return {'ordinary_count_exclusion':True},None
  gain=min(w[i] for i in used);total+=gain;groups.append({'faces':used,'weighted_loss':gain});proofs.append({'active':active[:],'proof':solver.proof});active=[i for i in active if i not in used]
 r={'directions':edge['directions'],'bounds':m['count_bounds'],'source_edge':edge['source_edge'],'share_lower':total,'cores':len(groups),'upper_bounds_only':lower_zero}
 return r,{'meta':m,'base_clauses':base,'face_clauses':faces,'face_weights':w,'groups':groups,'proofs':proofs}

if __name__=='__main__':
 E={e['source_edge']:e for e in json.loads((H/'filtered_critical_edges.json').read_text())};ids=json.loads((H/'bucket_excess_probe.json').read_text())['zero_gain_cycle'];rows=[];O=H/'upper_share_certificates';O.mkdir(exist_ok=True)
 for offset,k in enumerate(ids):
  r,proof=pack(E[k],True);r['offset']=offset;rows.append(r)
  if proof:
   with gzip.open(O/f'offset{offset}.json.gz','wt') as f:json.dump(proof,f,separators=(',',':'))
  print(json.dumps(r),flush=True)
 (H/'upper_share_rules.json').write_text(json.dumps(rows,indent=2)+'\n')
