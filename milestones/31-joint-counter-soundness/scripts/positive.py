"""Look for a local witness meeting the proposed case-2 lower bound."""
import json,time
from certify import HERE,ROOT,BOUNDS,TaggedEncoding,window,candidates,joint_literals,Cadical153,census,prior
for cap in [29,30]:
    ds=candidates()[2]['dirs'];W=window(ds);enc=TaggedEncoding(W,BOUNDS,radius=4)
    enc.atmost(joint_literals(enc,W),cap,('ends',))
    cuts=json.loads((HERE/'data/search-2.json').read_text())['cycle_cuts']
    for cc in cuts:enc.add([-enc.var[v] for v in cc],('cut',))
    t=time.monotonic();status='UNKNOWN';selected=None;report=None;extra=[]
    with Cadical153(bootstrap_with=enc.clauses) as solver:
        while time.monotonic()-t<30:
            solver.conf_budget(10000);ok=solver.solve_limited()
            if ok is None:continue
            if not ok:status='UNSAT';break
            model=solver.get_model();S={v for v in enc.ball if model[enc.var[v]-1]>0};c=census(S,9,W[1:-1])
            if not c['cycles']:
                selected=sorted(S);status='SAT';report=prior.census(dict(dirs=ds,alpha=BOUNDS,selected=selected));break
            for cc in c['cycles']:
                prior.check_cut(cc);extra.append(cc);solver.add_clause([-enc.var[v] for v in cc])
    row=dict(case=2,dirs=ds,alpha=BOUNDS,cap=cap,status=status,selected=selected,census=report,cycle_cuts=cuts+extra,seconds=time.monotonic()-t)
    (HERE/f'data/positive-2-{cap}.json').write_text(json.dumps(row,indent=2)+'\n')
    print(cap,status,report['alpha'] if report else '',flush=True)
    if status=='SAT':break
