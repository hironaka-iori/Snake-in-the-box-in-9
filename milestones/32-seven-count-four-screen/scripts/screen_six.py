"""Test whether six equal counts suffice, after all seven-centre tests excluded."""
import hashlib,json,sys,time
from pathlib import Path
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/'milestones/29-overlapping-share-windows/scripts'))
from joint import window,TaggedEncoding,Cadical153,census
outdir=HERE/'data/six';outdir.mkdir(parents=True,exist_ok=True)
shapes=[()]
for length in range(7):
    shapes=[d+(a,) for d in shapes for a in range(min(max(d,default=-1)+2,9))
            if len(set(w:=window(d+(a,))))==len(w) and
            all((w[i]^w[j]).bit_count()!=1 for i in range(len(w)) for j in range(i+2,len(w)))]
assert len(shapes)==34
(outdir/'shapes.json').write_text(json.dumps(shapes,indent=2)+'\n')
for i,ds in enumerate(shapes):
    path=outdir/f'window-{i:03d}.json'
    if path.exists():continue
    W=window(ds);enc=TaggedEncoding(W,[(4,4)]*6,radius=4);t=time.monotonic();cuts=[];status='UNKNOWN';selected=None;report=None
    with Cadical153(bootstrap_with=enc.clauses) as solver:
        while time.monotonic()-t<10:
            solver.conf_budget(10000);ok=solver.solve_limited()
            if ok is None:continue
            if not ok:status='UNSAT';break
            model=solver.get_model();S={v for v in enc.ball if model[enc.var[v]-1]>0};c=census(S,9,W[1:-1])
            if not c['cycles']:
                selected=sorted(S);c.pop('degree');report=c;status='SAT';break
            for cc in c['cycles']:cuts.append(cc);solver.add_clause([-enc.var[v] for v in cc])
    row=dict(dirs=ds,alpha=[[4,4]]*6,status=status,seconds=time.monotonic()-t,selected=selected,census=report,cycle_cuts=cuts,
             script_sha256_lf=hashlib.sha256(Path(__file__).read_bytes().replace(b'\r\n',b'\n')).hexdigest())
    path.write_text(json.dumps(row,indent=2)+'\n');print(i,ds,status,flush=True)
    if status=='SAT':break
