"""Proof-producing lower bound via a safe linear minorant of five-center share12.
Each empty face contributes once per charged center at distance one; this is a
lower bound because floor(12*E(q)/d(q)) >= E(q) for1<=d(q)<=9.
"""
from pathlib import Path
import json,sys,gzip,argparse
H=Path(__file__).resolve().parent;sys.path.insert(0,str(H));from zero_share_probe import build
sys.path[:0]=[str(H.parent/'branch241-review'),str(H.parent/'branch241-next/encoding')]
from pb_binary import BinaryCNF
from solver_plus import Solver
from rup_check import check
ap=argparse.ArgumentParser();ap.add_argument('--offset',type=int,default=0);ap.add_argument('--cap',type=int,default=15);ap.add_argument('--seconds',type=float,default=20);a=ap.parse_args();base={e['source_edge']:e for e in json.loads((H/'filtered_critical_edges.json').read_text())};eid=json.loads((H/'bucket_excess_probe.json').read_text())['zero_gain_cycle'][a.offset];E,meta=build(base[eid]);cs=E.clauses[:meta['base_clauses']];C=BinaryCNF();C.nv=E.nv;C.one=C.fresh();C.clauses=cs+[[C.one]];C.gates=[];C.cache={};inverse={var:v for v,var in E.var.items()};terms=[];face_data=[]
for clause in E.clauses[meta['base_clauses']:]:
 F=[inverse[z] for z in clause];weight=sum(any((c^q).bit_count()==1 for q in F) for c in meta['charged_centres']);assert weight>=1;lit=C.AND(*[-z for z in clause]);terms.append((lit,weight));face_data.append({'vertices':F,'weight':weight,'literal':lit})
C.clauses.append([C.leq_binary(terms,a.cap)]);S=Solver(C.clauses,C.nv,primary=E.var.values(),phase_true=[E.var[v] for v in meta['window']],restart='lbd');r=S.solve(a.seconds);proof=check(C.clauses,S.proof,require_empty=r['status']=='UNSAT');model=r.pop('model',None);receipt={'cap':a.cap,'source_edge':eid,'offset':a.offset,'meta':meta,'variables':C.nv,'clauses':len(C.clauses),'solver':r,'proof':proof,'claim_if_UNSAT':'five-center share12 at least cap+1, ordinary necessary-CNF proof; not Lean/global bound','new_global_bound':None}
if model is not None:
 assignment=set(model);assert all(any(l in assignment for l in c) for c in C.clauses);selected={v for v,z in E.var.items() if z in assignment};neighbors=lambda v:[v^(1<<k) for k in range(9)];value=0
 from itertools import combinations
 for c in meta['charged_centres']:
  for q in neighbors(c):
   degree=sum(v in selected for v in neighbors(q));assert degree>0
   empties=sum(not selected&{q,q^(1<<x),q^(1<<y),q^(1<<x)^(1<<y)} for x,y in combinations(range(9),2));value+=12*empties//degree
 receipt['SAT_local_actual_share']=value;receipt['SAT_is_full_snake']=False
O=H/'weighted_face_probes';O.mkdir(exist_ok=True);tag=('' if a.offset==0 else f'offset{a.offset}_')+f'cap{a.cap}'
with gzip.open(O/(tag+'.json.gz'),'wt') as f:json.dump({'clauses':C.clauses,'proof':S.proof,'face_data':face_data,'meta':meta,'model':model},f,separators=(',',':'))
(O/(tag+'_summary.json')).write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
