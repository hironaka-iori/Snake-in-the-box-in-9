"""Look for acyclic six-centre witnesses, to test the need for a seventh centre."""
import json,time
from joint import HERE,TaggedEncoding,Cadical153,candidates,dkey,window,census
for i,ds in enumerate(sorted({dkey(c['dirs'][s:s+7]) for c in candidates() for s in [0,1]})):
    W=window(ds);enc=TaggedEncoding(W,[(4,4)]*6,radius=4);t=time.monotonic();deadline=t+60
    cuts=[];status='UNKNOWN';selected=None;report=None
    with Cadical153(bootstrap_with=enc.clauses) as solver:
        while time.monotonic()<deadline:
            solver.conf_budget(10000);ok=solver.solve_limited()
            if ok is None:continue
            if not ok:status='UNSAT';break
            model=solver.get_model();S={v for v in enc.ball if model[enc.var[v]-1]>0}
            report=census(S,9,W[1:-1])
            if not report['cycles']:status='SAT';selected=sorted(S);report.pop('degree');break
            for cc in report['cycles']:solver.add_clause([-enc.var[v] for v in cc]);cuts.append(cc)
    row=dict(dirs=ds,alpha=[[4,4]]*6,status=status,selected=selected,census=report if selected else None,cycle_cuts=cuts,seconds=time.monotonic()-t)
    (HERE/'data'/f'six-witness-{i}.json').write_text(json.dumps(row,indent=2)+'\n')
    print(i,status,'cycles',len(cuts),'seconds',row['seconds'],flush=True)
