"""Test the sixteen selected short keys, first with monotone upper bounds."""
from pathlib import Path
import gzip,json,sys,time
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/'milestones/29-overlapping-share-windows/scripts'))
from joint import TaggedEncoding,window,Cadical153,census
for d in ['data','logs','lean','build','certificates']:(HERE/d).mkdir(parents=True,exist_ok=True)
selected=json.loads(gzip.decompress((ROOT/'milestones/71-proved-rule-conditional-pressure/data/old-selection.json.gz').read_bytes()))
keys=[dict(basis_id=i,dirs=w,counts=c) for i,(w,c) in zip(selected['selected_ids'],selected['keys']) if len(c)==4]
(HERE/'data/targets.json').write_text(json.dumps(keys,indent=2)+'\n')
def solve(row,mode,seconds=10):
    name=f"key-{row['basis_id']}-{mode}";bounds=[(0,c) if mode=='caps' else (c,c) for c in row['counts']]
    start=time.monotonic();W=window(row['dirs']);e=TaggedEncoding(W,bounds,radius=4)
    cuts=[];status='UNKNOWN';selected=None
    with Cadical153(bootstrap_with=e.clauses) as solver:
        deadline=time.monotonic()+seconds
        while time.monotonic()<deadline:
            solver.conf_budget(10000);ok=solver.solve_limited()
            if ok is None:continue
            if not ok:status='UNSAT';break
            model=solver.get_model();S={v for v in e.ball if model[e.var[v]-1]>0};report=census(S,9,W[1:-1])
            if not report['cycles']:status='SAT';selected=sorted(S);break
            for cycle in report['cycles']:cuts.append(cycle);solver.add_clause([-e.var[v] for v in cycle])
    out=dict(**row,name=name,bounds=bounds,status=status,selected=selected,cycle_cuts=cuts,seconds=time.monotonic()-start,scope='Numerical necessary local conditions; no theorem until replay.')
    (HERE/f'data/{name}.json').write_text(json.dumps(out,indent=2)+'\n');print(name,status,round(out['seconds'],2),flush=True)
    return out
if __name__=='__main__':
    rows=[]
    for row in keys:
        capfile=HERE/f"data/key-{row['basis_id']}-caps.json"
        old=json.loads(capfile.read_text()) if capfile.exists() else None
        out=old if old and old['status'] in ('SAT','UNSAT') else solve(row,'caps')
        if out['status']!='UNSAT':
            exactfile=HERE/f"data/key-{row['basis_id']}-exact.json"
            old=json.loads(exactfile.read_text()) if exactfile.exists() else None
            out=old if old and old['status'] in ('SAT','UNSAT') else solve(row,'exact')
        rows.append(out)
    (HERE/'data/probes.json').write_text(json.dumps(rows,indent=2)+'\n')
