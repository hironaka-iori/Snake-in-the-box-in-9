"""Test the count-free cap-15 cyclic control after valid cycle exclusions."""
from pathlib import Path
import json,sys,time
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[2]
sys.path.insert(0,str(ROOT/'milestones/29-overlapping-share-windows/scripts'))
from joint import window,Cadical153,census
sys.path.insert(0,str(ROOT/'milestones/28-direct-share-certificates/scripts'))
from tagged_share import TaggedShare
r=json.loads((HERE/'data/general3-cap15-certificate.json').read_text())
control=json.loads((HERE/'data/cap15-cyclic-control.json').read_text())
ds=r['directions'];bounds=r['bounds'];enc=TaggedShare(ds,bounds,15)
cuts=control['cycles'].copy();start=time.monotonic();status='UNKNOWN';selected=None;report=None
with Cadical153(bootstrap_with=enc.clauses) as solver:
 for c in cuts:solver.add_clause([-enc.var[v] for v in c])
 while time.monotonic()-start<30:
  solver.conf_budget(10000);ok=solver.solve_limited()
  if ok is None:continue
  if not ok:status='UNSAT';break
  model=solver.get_model();S={v for v in enc.ball if model[enc.var[v]-1]>0};report=census(S,9,window(ds)[1:-1]);report.pop('degree')
  if not report['cycles']:status='SAT_ACYCLIC';selected=sorted(S);break
  for cycle in report['cycles']:cuts.append(cycle);solver.add_clause([-enc.var[v] for v in cycle])
out=dict(directions=ds,bounds=bounds,cap=15,status=status,selected=selected,census=report,cycle_cuts=cuts,seconds=time.monotonic()-start,scope='Cycle-cut local test only; no Lean certificate or complete-snake realization.')
(HERE/'data/cap15-cycle-cut-probe.json').write_text(json.dumps(out,indent=2)+'\n')
print(status,'cycle cuts',len(cuts),'seconds',out['seconds'],flush=True)
