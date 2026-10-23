"""Positive five-centre control and fixed-selection independent validation."""
import json,sys,time,importlib.util
from pathlib import Path
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/'milestones/29-overlapping-share-windows/scripts'))
from joint import TaggedEncoding,window,Cadical153,census
from direct import solve
spec=importlib.util.spec_from_file_location('prior',ROOT/'milestones/28-direct-share-certificates/scripts/verify.py')
prior=importlib.util.module_from_spec(spec);spec.loader.exec_module(prior)
ds=[0,1,2,3,0,4];W=window(ds);bounds=[[4,4]]*5;enc=TaggedEncoding(W,bounds,radius=4)
t=time.monotonic();cuts=[];selected=None;status='UNKNOWN';report=None
with Cadical153(bootstrap_with=enc.clauses) as solver:
    while time.monotonic()-t<30:
        solver.conf_budget(10000);ok=solver.solve_limited()
        if ok is None:continue
        if not ok:status='UNSAT';break
        model=solver.get_model();S={v for v in enc.ball if model[enc.var[v]-1]>0};c=census(S,9,W[1:-1])
        if not c['cycles']:
            selected=sorted(S);status='SAT';report=prior.census(dict(dirs=ds,alpha=bounds,selected=selected));break
        for cc in c['cycles']:prior.check_cut(cc);cuts.append(cc);solver.add_clause([-enc.var[v] for v in cc])
row=dict(dirs=ds,alpha=bounds,status=status,selected=selected,census=report,cycle_cuts=cuts,seconds=time.monotonic()-t)
(HERE/'data/five-positive.json').write_text(json.dumps(row,indent=2)+'\n');print('SAT control',status,flush=True)
if selected:
    independent=solve(dict(dirs=ds,alpha=bounds),20,fixed=set(selected))
    (HERE/'data/five-fixed-cp.json').write_text(json.dumps(independent,indent=2)+'\n')
    print('Fixed independent CP control',independent['status'],flush=True)
