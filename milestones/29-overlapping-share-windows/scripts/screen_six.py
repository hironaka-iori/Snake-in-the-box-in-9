"""Short, inconclusive screen of the two six-centre precursor shapes."""
import json,time
from joint import HERE,TaggedEncoding,Cadical153,candidates,dkey,window
rows=[]
for ds in sorted({dkey(c['dirs'][s:s+7]) for c in candidates() for s in [0,1]}):
    enc=TaggedEncoding(window(ds),[(4,4)]*6,radius=4);t=time.monotonic()
    with Cadical153(bootstrap_with=enc.clauses) as solver:
        solver.conf_budget(50000);ok=solver.solve_limited()
    r=dict(dirs=ds,status='UNSAT' if ok is False else 'SAT_RELAXED' if ok else 'UNKNOWN',seconds=time.monotonic()-t)
    rows.append(r);print(r,flush=True)
(HERE/'data/six-centre-screen.json').write_text(json.dumps(rows,indent=2)+'\n')
