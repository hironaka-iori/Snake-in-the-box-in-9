"""Probe only a bounded set of surviving critical windows; reuse earlier decisive controls."""
from pathlib import Path
import json,sys,time
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[2];OLD=HERE.parent/'critical-charge'
sys.path.insert(0,str(ROOT/'milestones/29-overlapping-share-windows/scripts'))
from joint import TaggedEncoding,window,Cadical153,census
sys.path.insert(0,str(ROOT/'milestones/28-direct-share-certificates/scripts'))
from tagged_share import TaggedShare

for tag,ds in [('distinct',[0,1,2,3,4,5]),('return',[0,1,2,0,3,2]),('split',[0,1,2,3,1,4])]:
 bounds=[(0,21)]*5;enc=TaggedShare(ds,bounds,0);start=time.monotonic();cuts=[];status='UNKNOWN';selected=None;report=None
 with Cadical153(bootstrap_with=enc.clauses) as solver:
  while time.monotonic()-start<15:
   solver.conf_budget(10000);ok=solver.solve_limited()
   if ok is None:continue
   if not ok:status='UNSAT';break
   model=solver.get_model();S={v for v in enc.ball if model[enc.var[v]-1]>0};report=census(S,9,window(ds)[1:-1]);report.pop('degree')
   if not report['cycles']:status='SAT';selected=sorted(S);break
   for cycle in report['cycles']:cuts.append(cycle);solver.add_clause([-enc.var[v] for v in cycle])
 out=dict(directions=ds,bounds=bounds,cap=0,status=status,selected=selected,census=report,cycle_cuts=cuts,seconds=time.monotonic()-start,scope='Unconditioned local zero-share test. Solver result only, no theorem.')
 (HERE/f'data/general-{tag}.json').write_text(json.dumps(out,indent=2)+'\n');print(tag,status,report['alpha'] if selected else None,flush=True)
