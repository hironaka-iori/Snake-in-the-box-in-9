"""Broader local tests; every solver result is distinct from a Lean theorem."""
from pathlib import Path
import itertools,json,sys,time
ROOT=Path(__file__).resolve().parents[3];HERE=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'milestones/29-overlapping-share-windows/scripts'))
from joint import TaggedEncoding,window,Cadical153,census
DIRS=[0,1,2,3,4,2,0,3];CAPS=[2,21,21,21,3,5,2]

def solve(name,caps,joint_cap=None,seconds=12):
 t=time.monotonic();W=window(DIRS);enc=TaggedEncoding(W,[(0,x) for x in caps],radius=4)
 if joint_cap is not None:
  lits=[]
  for j in (5,6):
   free=[d for d in range(9) if d not in (DIRS[j-1],DIRS[j])]
   lits += [-enc.var[W[j]^(1<<a)^(1<<b)] for a,b in itertools.combinations(free,2)]
  enc.atmost(lits,joint_cap,('ends',))
 status='UNKNOWN';cuts=[];selected=None;report=None
 with Cadical153(bootstrap_with=enc.clauses) as solver:
  while time.monotonic()-t<seconds:
   solver.conf_budget(10000);ok=solver.solve_limited()
   if ok is None:continue
   if not ok:status='UNSAT';break
   model=solver.get_model();S={v for v in enc.ball if model[enc.var[v]-1]>0}
   report=census(S,9,W[1:-1]);report.pop('degree')
   if report['cycles']:
    for c in report['cycles']:cuts.append(c);solver.add_clause([-enc.var[v] for v in c])
   else:
    status='SAT';selected=sorted(S)
    assert all(a<=b for a,b in zip(report['alpha'],caps))
    assert joint_cap is None or sum(report['alpha'][4:6])<=joint_cap
    break
 out=dict(name=name,directions=DIRS,caps=caps,joint_cap=joint_cap,status=status,selected=selected,census=report if selected else None,cycle_cuts=cuts,seconds=time.monotonic()-t,scope='Acyclic local model or solver exclusion; no full-snake existence and no new checked exclusion implied.')
 (HERE/'data'/f'{name}.json').write_text(json.dumps(out,indent=2)+'\n')
 print(name,status,report['alpha'] if selected else '',round(out['seconds'],2),flush=True)

if __name__=='__main__':
 (HERE/'data').mkdir(exist_ok=True)
 solve('four-bounds',CAPS)
 solve('outer-only',[2,21,21,21,21,21,2])
 for i in (0,4,5,6):
  caps=CAPS.copy();caps[i]+=1
  solve(f'relax-{i}',caps)
 for cap in (8,9,10):solve(f'sum-{cap}',[2,21,21,21,21,21,2],cap)
 solve('all-free',[21]*7)
 solve('first-only',[2,21,21,21,21,21,21])
 solve('last-only',[21,21,21,21,21,21,2])
 for a,b in ((1,3),(2,3),(3,2),(3,3),(1,4),(4,1),(2,4),(4,2),(3,4),(4,3),(4,4),
             (1,21),(21,1),(2,5),(2,6),(3,1),(5,1),(6,1),(7,1),(8,1),(9,1),(10,1),(11,1),(12,1)):
  solve(f'pair-{a}-{b}',[a,21,21,21,21,21,b],seconds=5)
