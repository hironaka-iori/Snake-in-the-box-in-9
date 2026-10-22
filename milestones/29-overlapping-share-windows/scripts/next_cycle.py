"""Exploratory next-cycle test: compare exact six with the coarse 6..21 symbol."""
import json,time
from joint import HERE,TaggedEncoding,Cadical153,candidates,window,census

patterns=[[3,3,6,3,3,6,3],[3,6,3,3,6,3,3],[6,3,3,6,3,3,6],[6,3,3,6,3,3,6]]
for mode in ['exact','interval']:
    for i,case in enumerate(candidates()):
        bounds=[(s,21 if s==6 and mode=='interval' else s) for s in patterns[i]]
        W=window(case['dirs']);enc=TaggedEncoding(W,bounds,radius=4);t=time.monotonic();deadline=t+15
        cuts=[];status='UNKNOWN';selected=None;report=None
        with Cadical153(bootstrap_with=enc.clauses) as solver:
            while time.monotonic()<deadline:
                solver.conf_budget(10000);ok=solver.solve_limited()
                if ok is None:continue
                if not ok:status='UNSAT';break
                m=solver.get_model();S={v for v in enc.ball if m[enc.var[v]-1]>0};report=census(S,9,W[1:-1])
                if not report['cycles']:status='SAT';selected=sorted(S);report.pop('degree');break
                for cc in report['cycles']:solver.add_clause([-enc.var[v] for v in cc]);cuts.append(cc)
        row=dict(dirs=case['dirs'],alpha=bounds,status=status,selected=selected,census=report if selected else None,cycle_cuts=cuts,seconds=time.monotonic()-t)
        (HERE/'data'/f'next-{mode}-{i}.json').write_text(json.dumps(row,indent=2)+'\n')
        print(mode,i,status,'cuts',len(cuts),'seconds',row['seconds'],flush=True)
