"""Separate ordinary window exclusions from exclusions that need the share cap."""
import json,sys,time
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3];HERE=Path(__file__).resolve().parents[1]
sys.path[:0]=[str(ROOT/'work/share_packages'),str(ROOT/'work/solver_packages'),str(ROOT/'milestones/10-window-aggregate/scripts')]
from gen_lean_sat import TaggedEncoding
from wincert import window_from_dirs,cycles_of
from pysat.solvers import Cadical153

def main():
    rows=[];rec=json.loads((HERE/'data/cache-obstruction.json').read_text())['records']
    for i,r in enumerate(rec):
        ds,al=r['five_window_key'];t=time.monotonic();enc=TaggedEncoding(window_from_dirs(ds),al,radius=4)
        status='UNKNOWN';witness=None;cuts=[]
        with Cadical153(bootstrap_with=enc.clauses) as s:
            deadline=time.monotonic()+10
            while time.monotonic()<deadline:
                s.conf_budget(10000);ok=s.solve_limited()
                if ok is None:continue
                if not ok:status='UNSAT';break
                m=s.get_model();selected=[v for v in enc.ball if m[enc.var[v]-1]>0];cycles=cycles_of(selected)
                if not cycles:status='SAT';witness=selected;break
                for cyc in cycles:s.add_clause([-enc.var[v] for v in cyc]);cuts.append(cyc)
        rows.append(dict(row=i,dirs=ds,alpha=al,status=status,selected=witness,cycle_cuts=cuts,seconds=round(time.monotonic()-t,3)))
        (HERE/'data/plain-screen.json').write_text(json.dumps(dict(complete=len(rows)==len(rec),rows=rows),indent=2)+'\n')
        print(i,status,'cycles',len(cuts),flush=True)
if __name__=='__main__':main()
