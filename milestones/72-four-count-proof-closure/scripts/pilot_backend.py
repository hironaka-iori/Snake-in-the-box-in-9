"""Bounded independent solver-version pilot for a timed-out exact count case."""
from pathlib import Path
import json,sys,time
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/'milestones/29-overlapping-share-windows/scripts'))
from joint import TaggedEncoding,window,Cadical153,census
case=next(c for c in json.loads((HERE/'data/cases.json').read_text()) if c['number']==7204)
prior=json.loads((HERE/f"data/{case['probe']}.json").read_text())
W=window(case['dirs']);e=TaggedEncoding(W,case['bounds'],radius=4);cuts=list(prior['cycle_cuts'])
for cycle in cuts:e.add([-e.var[v] for v in cycle],('cut',))
started=time.monotonic();status='UNKNOWN';selected=None;proof=None
with Cadical153(bootstrap_with=e.clauses,with_proof=True) as solver:
 while time.monotonic()-started<60:
  solver.conf_budget(10000);ok=solver.solve_limited()
  if ok is None:continue
  if not ok:status='UNSAT';proof=solver.get_proof();break
  m=solver.get_model();S={v for v in e.ball if m[e.var[v]-1]>0};r=census(S,9,W[1:-1])
  if not r['cycles']:status='SAT';selected=sorted(S);break
  for cycle in r['cycles']:
   clause=[-e.var[v] for v in cycle];cuts.append(cycle);e.add(clause,('cut',));solver.add_clause(clause)
 stats=solver.accum_stats()
result=dict(case=7204,status=status,dirs=case['dirs'],bounds=case['bounds'],cycle_cuts=cuts,selected=selected,seconds=time.monotonic()-started,solver='PySAT Cadical153 with proof output',stats=stats,scope='Solver evidence only; a proof requires independent checking and Lean replay.')
if proof is not None:
 prefix=HERE/'certificates/pilot7204'
 prefix.with_suffix('.full.cnf').write_text(f'p cnf {e.nv} {len(e.clauses)}\n'+''.join(' '.join(map(str,c))+' 0\n' for c in e.clauses))
 prefix.with_suffix('.drat').write_text('\n'.join(proof)+'\n');result['proof_lines']=len(proof)
(HERE/'data/backend-pilot-7204.json').write_text(json.dumps(result,indent=2)+'\n');print({k:v for k,v in result.items() if k not in ['cycle_cuts','selected']},flush=True)
