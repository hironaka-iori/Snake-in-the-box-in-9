"""Reproduce ordinary local forests independently of the share encoder."""
from pathlib import Path
import concurrent.futures,json,sys,time
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/'milestones/29-overlapping-share-windows/scripts'))
from joint import TaggedEncoding,window,Cadical153,census
def task(item):
 i,row=item;file=HERE/f'data/controls/w{i:02d}.json';file.parent.mkdir(parents=True,exist_ok=True)
 if file.exists():return json.loads(file.read_text())
 t=time.monotonic();ds=row['directions'];W=window(ds);bounds=[[6,21] if c==6 else [c,c] for c in row['counts']];e=TaggedEncoding(W,bounds,radius=4)
 status='UNKNOWN';selected=None;report=None;cuts=[]
 with Cadical153(bootstrap_with=e.clauses) as solver:
  while time.monotonic()-t<15:
   solver.conf_budget(10000);ok=solver.solve_limited()
   if ok is None:continue
   if not ok:status='UNSAT';break
   assignment=solver.get_model();S={v for v in e.ball if assignment[e.var[v]-1]>0};r=census(S,9,W[1:-1]);r.pop('degree')
   if r['cycles']:
    for cycle in r['cycles']:cuts.append(cycle);solver.add_clause([-e.var[v] for v in cycle])
   else:status='SAT';selected=sorted(S);report=r;break
 out=dict(name=f'w{i:02d}',directions=ds,counts=row['counts'],bounds=bounds,status=status,selected=selected,census=report,cycle_cuts=cuts,seconds=time.monotonic()-t)
 file.write_text(json.dumps(out,indent=2)+'\n');print(out['name'],status,report['total_share'] if report else None,flush=True);return out
if __name__=='__main__':
 rows=json.loads((HERE/'data/windows.json').read_text())
 with concurrent.futures.ProcessPoolExecutor(max_workers=2) as pool:results=list(pool.map(task,enumerate(rows)))
 (HERE/'data/controls.json').write_text(json.dumps([{k:v for k,v in r.items() if k not in ['selected','census','cycle_cuts']} for r in results],indent=2)+'\n')
