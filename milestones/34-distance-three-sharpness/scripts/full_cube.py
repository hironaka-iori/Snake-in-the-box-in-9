"""Strengthen pair tests to full-cube degree conditions and separate cycles."""
import hashlib,json,sys,time
from pathlib import Path
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/'milestones/33-distance-three-singletons/scripts'))
from certify import TaggedEncoding,window,candidates,Cadical153,census,joint_literals,BOUNDS,prior

def probe(i,cap,seconds=20):
 ds=candidates()[i]['dirs'];W=window(ds);enc=TaggedEncoding(W,BOUNDS,radius=9);assert len(enc.ball)==512
 enc.atmost(joint_literals(enc,W),cap,('ends',));cuts=[];status='UNKNOWN';chosen=None;report=None;path=None
 t=time.monotonic()
 with Cadical153(bootstrap_with=enc.clauses) as solver:
  while time.monotonic()-t<seconds:
   solver.conf_budget(3000);ok=solver.solve_limited()
   if ok is None:continue
   if not ok:status='UNSAT';break
   m=solver.get_model();S={v for v in enc.ball if m[enc.var[v]-1]>0};rep=census(S,9,W[1:-1]);rep.pop('degree')
   if not rep['cycles']:
    parts=prior.components(S);assert len(parts)==1
    ends=[v for v in S if sum(w in S for w in prior.neighbors(v))==1];assert len(ends)==2
    path=[ends[0]]
    while len(path)<len(S):
     nxt=[v for v in prior.neighbors(path[-1]) if v in S and (len(path)==1 or v!=path[-2])];assert len(nxt)==1;path.append(nxt[0])
    assert len(path)==len(set(path)) and all(((u^path[j]).bit_count()==1)==(j==k+1) for k,u in enumerate(path) for j in range(k+1,len(path)))
    chosen=sorted(S);report=rep;status='SAT';break
   for cc in rep['cycles']:
    prior.check_cut(cc);cuts.append(cc);solver.add_clause([-enc.var[v] for v in cc])
 row=dict(case=i,dirs=ds,alpha=BOUNDS,cap=cap,radius=9,status=status,seconds=time.monotonic()-t,selected=chosen,census=report,vertex_sequence=path,cycle_cuts=cuts,
  scope='Full-cube necessary conditions; UNSAT awaits Lean replay. A cycle-free SAT selection is independently checked as one snake.')
 (HERE/f'data/full-{i}-cap-{cap}.json').write_text(json.dumps(row,indent=2)+'\n')
 print(i,cap,status,'cuts',len(cuts),'length',None if path is None else len(path)-1,flush=True)
 return status
for i,caps in [(0,[10,11,12,13,14,15]),(1,[9,10,11,12,13,14])]:
 for cap in caps:
  if probe(i,cap)!='UNSAT':break
