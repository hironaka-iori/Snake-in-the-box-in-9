"""Probe only a bounded set of surviving critical windows; reuse earlier decisive controls."""
from pathlib import Path
import json,sys,time
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[2];OLD=HERE.parent/'critical-charge'
sys.path.insert(0,str(ROOT/'milestones/29-overlapping-share-windows/scripts'))
from joint import TaggedEncoding,window,Cadical153,census
sys.path.insert(0,str(ROOT/'milestones/28-direct-share-certificates/scripts'))
from tagged_share import TaggedShare
read=lambda p:json.loads(p.read_text());rows=read(HERE/'data/windows.json');targets=[0,1,2,3,4,405,448,471,474,462,467,468]
(HERE/'data/probes').mkdir(exist_ok=True)
cache={}
for f in (OLD/'data/screen').glob('*-native.json'):
 row=read(f)
 if row['status'] in ['SAT','UNSAT']:cache[(tuple(row['directions']),tuple(row['counts']))]=row
for i in targets:
 row=rows[i];ds=row['directions'];cs=row['counts'];bounds=[(6,21) if c==6 else (c,c) for c in cs]
 plain=cache.get((tuple(ds),tuple(cs)))
 for cap in ([None] if plain is None else [])+[0,95]:
  if cap is not None and plain and plain['status']=='UNSAT':continue
  path=HERE/'data/probes'/f'w{i:03d}-'+Path('x') if False else HERE/'data/probes'/f'w{i:03d}-{cap}.json'
  if path.exists():continue
  e=TaggedEncoding(window(ds),bounds,radius=4) if cap is None else TaggedShare(ds,bounds,cap)
  cuts=[];status='UNKNOWN';selected=None;report=None;start=time.monotonic()
  with Cadical153(bootstrap_with=e.clauses) as solver:
   while time.monotonic()-start<10:
    solver.conf_budget(10000);ok=solver.solve_limited()
    if ok is None:continue
    if not ok:status='UNSAT';break
    model=solver.get_model();S={v for v in e.ball if model[e.var[v]-1]>0};report=census(S,9,window(ds)[1:-1]);report.pop('degree')
    if not report['cycles']:status='SAT';selected=sorted(S);break
    for cycle in report['cycles']:cuts.append(cycle);solver.add_clause([-e.var[v] for v in cycle])
  result=dict(index=i,directions=ds,counts=cs,bounds=bounds,cap=cap,status=status,selected=selected,census=report,cycle_cuts=cuts,seconds=time.monotonic()-start,scope='Numerical local probe only; no universal theorem or complete snake witness claimed.')
  path.write_text(json.dumps(result,indent=2)+'\n');print(i,cap,status,report['total_share'] if selected else '',flush=True)
  if cap is None:
   plain=result
   if status=='UNSAT':break
