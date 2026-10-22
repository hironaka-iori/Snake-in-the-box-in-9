"""Solver-only tests of the sum of the three high singleton counts."""
import itertools,json,sys,time
from pathlib import Path
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/'milestones/29-overlapping-share-windows/scripts'))
from joint import TaggedEncoding,Cadical153,candidates,window,census

for i in [3,2]:
    ds=candidates()[i]['dirs'];W=window(ds);bounds=[(6,21),(3,3),(3,3),(6,21),(3,3),(3,3),(6,21)]
    for cap in [19,20,21,24]:
        enc=TaggedEncoding(W,bounds,radius=4);lits=[]
        for j in [1,4,7]:
            c=W[j];used={(c^W[j-1]).bit_length()-1,(c^W[j+1]).bit_length()-1}
            lits.extend(-enc.var[c^(1<<a)^(1<<b)] for a,b in itertools.combinations(range(9),2) if a not in used and b not in used)
        assert len(lits)==63
        # Experimental counter kind: this extra premise has no Lean clause tag here.
        enc.atmost(lits,cap,('jointSum',0))
        t=time.monotonic();deadline=t+20;status='UNKNOWN';S=None;cuts=[];report=None
        with Cadical153(bootstrap_with=enc.clauses) as solver:
            while time.monotonic()<deadline:
                solver.conf_budget(10000);ok=solver.solve_limited()
                if ok is None:continue
                if not ok:status='UNSAT';break
                m=solver.get_model();sel={v for v in enc.ball if m[enc.var[v]-1]>0};report=census(sel,9,W[1:-1])
                assert sum(report['alpha'][j] for j in [0,3,6])<=cap
                if not report['cycles']:status='SAT';S=sorted(sel);report.pop('degree');break
                for cc in report['cycles']:solver.add_clause([-enc.var[v] for v in cc]);cuts.append(cc)
        row=dict(case=i,dirs=ds,alpha=bounds,cap=cap,status=status,selected=S,census=report if S else None,cycle_cuts=cuts,seconds=time.monotonic()-t)
        (HERE/'data'/f'excess-{i}-{cap}.json').write_text(json.dumps(row,indent=2)+'\n')
        print(i,cap,status,report['alpha'] if S else '',flush=True)
