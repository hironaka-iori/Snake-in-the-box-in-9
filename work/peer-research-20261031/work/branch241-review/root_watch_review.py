"""Targeted regressions for permanent-root watch pruning and compositional RUP."""
import json
from pathlib import Path
from solver import Solver
from rup_check import check
chain=[[1]]+[[-i,i+1] for i in range(1,20)]
residue=[[-20,21,22],[-20,-21,22],[-20,21,-22],[-20,-21,-22]]
rows=[]
for name,cs,status in [('root_chain_conflict',chain+[[-20]],'UNSAT'),('root_conditional_conflict',chain+residue,'UNSAT'),('root_conditional_sat',chain+residue[:-1],'SAT')]:
 s=Solver(cs);r=s.solve();assert r['status']==status
 if status=='UNSAT':
  full=check(cs,s.proof);k=len(s.proof)//2;prefix=check(cs,s.proof[:k],require_empty=False)
  tail=check(cs+[p['clause'] for p in s.proof[:k]],s.proof[k:]);assert prefix['unit_hints_checked']+tail['unit_hints_checked']==full['unit_hints_checked']
  r['proof']=full
 else:
  a={abs(l):l>0 for l in r.pop('model')};assert all(any(a[abs(l)]==(l>0) for l in c) for c in cs)
 r['case']=name;rows.append(r)
(Path(__file__).parent/'root_watch_results.json').write_text(json.dumps(rows,indent=2));print(json.dumps(rows,indent=2))
