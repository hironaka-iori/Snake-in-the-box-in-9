"""Probe only a bounded set of surviving critical windows; reuse earlier decisive controls."""
from pathlib import Path
import json,sys,time
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[2];OLD=HERE.parent/'critical-charge'
sys.path.insert(0,str(ROOT/'milestones/29-overlapping-share-windows/scripts'))
from joint import TaggedEncoding,window,Cadical153,census
sys.path.insert(0,str(ROOT/'milestones/28-direct-share-certificates/scripts'))
from tagged_share import TaggedShare

for tag,ds,cap in [('one',[0,1],0),('one',[0,1],5),('one',[0,1],11),('distinct',[0,1,2,3,4,5],11),('return',[0,1,2,0,3,2],11),('split',[0,1,2,3,1,4],11)]:
 bounds=[(0,21)]*(len(ds)-1);enc=TaggedShare(ds,bounds,cap);start=time.monotonic();cuts=[];status='UNKNOWN';selected=None;report=None
 with Cadical153(bootstrap_with=enc.clauses) as solver:
  while time.monotonic()-start<8:
   solver.conf_budget(10000);ok=solver.solve_limited()
   if ok is None:continue
   if not ok:status='UNSAT';break
   model=solver.get_model();S={v for v in enc.ball if model[enc.var[v]-1]>0};report=census(S,9,window(ds)[1:-1]);report.pop('degree')
   if not report['cycles']:status='SAT';selected=sorted(S);break
   for cycle in report['cycles']:cuts.append(cycle);solver.add_clause([-enc.var[v] for v in cycle])
 out=dict(directions=ds,bounds=bounds,cap=cap,status=status,selected=selected,census=report,cycle_cuts=cuts,seconds=time.monotonic()-start,scope='Unconditioned local zero-share test. Solver result only, no theorem.')
 (HERE/f'data/general-{tag}-cap{cap}.json').write_text(json.dumps(out,indent=2)+'\n');print(tag,cap,status,report['alpha'] if selected else None,flush=True)
