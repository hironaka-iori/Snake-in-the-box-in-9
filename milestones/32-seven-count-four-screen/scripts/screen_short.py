"""Find the shorter surviving all-four shapes to reduce future proof coverage."""
import json,sys,time
from pathlib import Path
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/'milestones/29-overlapping-share-windows/scripts'))
from joint import TaggedEncoding,window,Cadical153,census
shapes=[()]
for length in range(6):
    shapes=[d+(a,) for d in shapes for a in range(min(max(d,default=-1)+2,9))
            if len(set(w:=window(d+(a,))))==len(w) and
            all((w[i]^w[j]).bit_count()!=1 for i in range(len(w)) for j in range(i+2,len(w)))]
    if length+1 not in [5,6]:continue
    for i,ds in enumerate(shapes):
        n=len(ds)-1;W=window(ds);enc=TaggedEncoding(W,[(4,4)]*n,radius=4)
        t=time.monotonic();cuts=[];selected=None;report=None;status='UNKNOWN'
        with Cadical153(bootstrap_with=enc.clauses) as solver:
            while time.monotonic()-t<10:
                solver.conf_budget(10000);ok=solver.solve_limited()
                if ok is None:continue
                if not ok:status='UNSAT';break
                m=solver.get_model();S={v for v in enc.ball if m[enc.var[v]-1]>0};c=census(S,9,W[1:-1])
                if not c['cycles']:
                    selected=sorted(S);c.pop('degree');report=c;status='SAT';break
                for cc in c['cycles']:cuts.append(cc);solver.add_clause([-enc.var[v] for v in cc])
        row=dict(dirs=ds,alpha=[[4,4]]*n,status=status,selected=selected,census=report,cycle_cuts=cuts,seconds=time.monotonic()-t)
        (HERE/f'data/short-{n}-{i}.json').write_text(json.dumps(row,indent=2)+'\n');print(n,i,ds,status,flush=True)
