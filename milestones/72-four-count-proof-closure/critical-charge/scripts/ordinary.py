"""Independent SAT checks of the representative windows, with cycle separation."""
from pathlib import Path
import json,sys,time
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[2]
sys.path.insert(0,str(ROOT/'milestones/29-overlapping-share-windows/scripts'))
from joint import TaggedEncoding,window,Cadical153,census
rows=json.loads((HERE/'data/windows.json').read_text());plan=json.loads((HERE/'data/screen-plan.json').read_text())
for index in plan['selected_windows']:
    path=HERE/f'data/screen/w{index:03d}-native.json'
    if path.exists():continue
    row=rows[index];bounds=[(6,21) if c==6 else (c,c) for c in row['counts']]
    W=window(row['directions']);e=TaggedEncoding(W,bounds,radius=4);cuts=[];status='UNKNOWN';selected=None;report=None;start=time.monotonic()
    with Cadical153(bootstrap_with=e.clauses) as solver:
        while time.monotonic()-start<12:
            solver.conf_budget(10000);ok=solver.solve_limited()
            if ok is None:continue
            if not ok:status='UNSAT';break
            model=solver.get_model();S={v for v in e.ball if model[e.var[v]-1]>0};report=census(S,9,W[1:-1]);report.pop('degree')
            if not report['cycles']:status='SAT';selected=sorted(S);break
            for cycle in report['cycles']:cuts.append(cycle);solver.add_clause([-e.var[v] for v in cycle])
    out=dict(window=index,directions=row['directions'],counts=row['counts'],bounds=bounds,status=status,selected=selected,census=report,cycle_cuts=cuts,seconds=time.monotonic()-start,scope='Native SAT result only; UNSAT needs proof replay. SAT describes a local acyclic configuration, not necessarily a complete snake.')
    path.write_text(json.dumps(out,indent=2)+'\n');print(index,status,report['total_share'] if selected else None,flush=True)
