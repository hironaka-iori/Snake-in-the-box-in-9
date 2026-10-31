"""Disjoint cores of zero-empty-face assumptions yield certified share lower bounds.
Each core proves at least one of its faces empty. Disjoint face sets avoid charging
one empty face twice. Every share12 summand floor(12 E/d) is >= E for 1<=d<=9.
"""
from pathlib import Path
import json,sys,gzip
H=Path(__file__).resolve().parent;sys.path.insert(0,str(H));from zero_share_probe import build
sys.path.insert(0,str(H.parent/'branch241-review'));from solver import Solver
from rup_check import check

def run(offset=0):
 edges={e['source_edge']:e for e in json.loads((H/'filtered_critical_edges.json').read_text())};cycle=json.loads((H/'bucket_excess_probe.json').read_text())['zero_gain_cycle'];edge=edges[cycle[offset%len(cycle)]];E,m=build(edge);base=E.clauses[:m['base_clauses']];face_clauses=E.clauses[m['base_clauses']:];inverse={var:v for v,var in E.var.items()};weights=[]
 for clause in face_clauses:
  F=[inverse[x] for x in clause];weights.append(sum(any((c^q).bit_count()==1 for q in F) for c in m['charged_centres']))
 active=list(range(len(face_clauses)));groups=[];seen=set();total=0;proofs=[]
 for round in range(100):
  cs=base+[face_clauses[i] for i in active];solver=Solver(cs,E.nv)
  if solver.root_conflict is None:break
  result=solver.solve(seconds=0);assert result['status']=='UNSAT';receipt=check(cs,solver.proof)
  used=sorted({active[h-len(base)-1] for step in solver.proof for h in step['hints'] if h>len(base)})
  if not used:raise ValueError('base counts alone unit-inconsistent: ordinary exclusion')
  assert not seen&set(used);seen.update(used);value=min(weights[i] for i in used);total+=value;groups.append({'faces':used,'weighted_incidence_loss':value,'rup':receipt});proofs.append({'active':active[:],'proof':solver.proof});active=[i for i in active if i not in seen]
 r={'source_edge':edge['source_edge'],'offset':offset,'counts':edge['counts'],'directions':edge['directions'],'disjoint_cores':len(groups),'proved_five_centre_share12_lower':total,'groups':groups,'domain_all_faces_complete':True,'scope':'ordinary CNF geometry plus checked RUP; no Lean or global bound'}
 out=H/'zero_share_probes';out.mkdir(exist_ok=True)
 with gzip.open(out/f'core_pack_offset{offset}.json.gz','wt') as f:json.dump({'base_clauses':base,'face_clauses':face_clauses,'face_weights':weights,'proofs':proofs,'meta':m},f,separators=(',',':'))
 (out/f'core_pack_offset{offset}_summary.json').write_text(json.dumps(r,indent=2)+'\n');return r
if __name__=='__main__':
 for k in range(8):
  r=run(k);print(json.dumps({x:y for x,y in r.items() if x!='groups'}),flush=True)
