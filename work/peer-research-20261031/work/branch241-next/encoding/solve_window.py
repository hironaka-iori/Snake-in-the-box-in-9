"""Optional project-style lazy-cycle search; requires working python-sat/CaDiCaL.
Cold DRUP export is NOT a Lean certificate. SAT denotes only a local model.
"""
import argparse,json,sys,time
from pathlib import Path
from github_query import build,REPO,HERE
from charge_fast import Geometry,Charges

def cycle_components(S):
 S=set(S);adj={x:[x^(1<<d) for d in range(9) if x^(1<<d) in S] for x in S};seen=set();out=[]
 for root in sorted(S):
  if root in seen:continue
  stack=[root];comp=[];seen.add(root)
  while stack:
   v=stack.pop();comp.append(v)
   for w in adj[v]:
    if w not in seen:seen.add(w);stack.append(w)
  if len(comp)>2 and all(len(adj[v])==2 for v in comp):out.append(sorted(comp))
 return out

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--cap',type=int,default=850);ap.add_argument('--centres',type=int,default=9);ap.add_argument('--bank',type=int,default=67);ap.add_argument('--max-rounds',type=int,default=10000);ap.add_argument('--out',type=Path,default=HERE/'solver_run');args=ap.parse_args()
 try:from pysat.solvers import Cadical153
 except ImportError:
  print('Solver unavailable. Use this script in the project CaDiCaL/python-sat environment; no search was run.');return 2
 bank=json.loads((REPO/'work/bank9.json').read_text());path=bank[args.bank]['vertex_sequence'][:args.centres+2];E,geo,remap,meta=build(path,args.cap);args.out.mkdir(parents=True,exist_ok=True);t=time.perf_counter();status='UNKNOWN';cuts=0
 with Cadical153(bootstrap_with=E.cnf.clauses) as solver:
  for round_index in range(args.max_rounds):
   if not solver.solve():status='UNSAT';break
   model=solver.get_model();assignment={abs(l):l>0 for l in model};assert E.cnf.satisfied(assignment)
   selected=[v for v,var in E.var.items() if assignment[var]];cycles=cycle_components(selected)
   exact=Charges(Geometry(9),selected).cheap()['r6plus'];assert sum(exact['values'][x] for x in E.centres)<=args.cap
   if not cycles:
    status='LOCAL_SAT';(args.out/'local_model.json').write_text(json.dumps({'selected':selected,'warning':'Local necessary-condition model only; not a certified global snake.'},indent=2));break
   for cyc in cycles:
    clause=[-E.var[v] for v in cyc];E.cnf.clauses.append(clause);solver.add_clause(clause);cuts+=1
   (args.out/'progress.json').write_text(json.dumps({'rounds':round_index+1,'cuts':cuts,'elapsed_seconds':time.perf_counter()-t}))
 with (args.out/'final.cnf').open('w') as f:
  f.write(f'p cnf {E.cnf.nv} {len(E.cnf.clauses)}\n')
  for c in E.cnf.clauses:f.write(' '.join(map(str,c))+' 0\n')
 if status=='UNSAT':
  # A fresh solve of the complete static formula, as required by the project's method.
  with Cadical153(bootstrap_with=E.cnf.clauses,with_proof=True) as cold:
   assert not cold.solve();proof=cold.get_proof()
  (args.out/'cold.drup').write_text('\n'.join(proof)+'\n')
 meta.update(status=status,cycle_cuts=cuts,elapsed_seconds=time.perf_counter()-t,certificate_checked=False,lean_checked=False)
 (args.out/'result.json').write_text(json.dumps(meta,indent=2));print(json.dumps(meta,indent=2));return 0
if __name__=='__main__':sys.exit(main())
