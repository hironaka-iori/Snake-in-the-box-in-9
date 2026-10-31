"""Independent projected-SAT and RUP checks of SolverPlus configurations.
The defaults/options are supplied via --configs to avoid coupling to implementation.
"""
from pathlib import Path
import argparse,itertools,random,json,time,importlib,inspect
from rup_check import check
H=Path(__file__).resolve().parent

def brute(clauses,n):
 for bits in range(1<<n):
  if all(any(bool(bits>>(abs(l)-1)&1)==(l>0) for l in c) for c in clauses):return True
 return False

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--configs',type=Path);ap.add_argument('--class-name',default='SolverPlus');args=ap.parse_args();module=importlib.import_module('solver_plus');Cls=getattr(module,args.class_name)
 configs=json.loads(args.configs.read_text()) if args.configs else [{}];rng=random.Random(94557329);cases=[]
 targeted=[([[1],[-1,2],[-2,3],[-3]],3),([[1,2],[-1,3],[-2,3],[-3,4],[-4,5],[-5,-1],[-5,-2]],5),([[1,-1],[1,1,2],[-1,2,2],[-2,3],[-3,4],[-4,-2]],4),([],3),([[]],3)]
 cases.extend((cs,n,brute(cs,n)) for cs,n in targeted)
 for _ in range(320):
  n=rng.randrange(3,10);clauses=[]
  for j in range(rng.randrange(2*n,7*n)):
   k=rng.choice((2,3,3,3,min(4,n)));vs=rng.sample(range(1,n+1),k);clauses.append([v*rng.choice((-1,1)) for v in vs])
  if rng.random()<.25:
   u=rng.randrange(1,n+1);clauses.append([u*rng.choice((-1,1))])
  cases.append((clauses,n,brute(clauses,n)))
 for holes in (3,4,5,6):
  pigeons=holes+1;v=lambda p,h:p*holes+h+1
  clauses=[[v(p,h) for h in range(holes)] for p in range(pigeons)]+[[-v(p,h),-v(q,h)] for h in range(holes) for p in range(pigeons) for q in range(p+1,pigeons)]
  cases.append((clauses,pigeons*holes,False))
 results=[];start=time.perf_counter()
 for cfg in configs:
  stats={'options':cfg,'cases':0,'SAT':0,'UNSAT':0,'checked_steps':0,'checked_hints':0,'max_restarts':0};t=time.perf_counter()
  for index,(clauses,n,expected) in enumerate(cases):
   original=[c[:] for c in clauses];solver=Cls(clauses,nvars=n,**cfg);result=solver.solve(seconds=10)
   assert result['status'] in ('SAT','UNSAT'),(cfg,index,result)
   assert (result['status']=='SAT')==expected,(cfg,index,clauses,result)
   assert clauses==original,'solver mutated caller input'
   checked=check(original,solver.proof,require_empty=not expected)
   if expected:
    model={abs(l):l>0 for l in result['model']};assert all(any(model[abs(l)]==(l>0) for l in c) for c in original),(cfg,index,'bad model')
   stats['cases']+=1;stats[result['status']]+=1;stats['checked_steps']+=checked['RUP_steps_checked'];stats['checked_hints']+=checked['unit_hints_checked'];stats['max_restarts']=max(stats['max_restarts'],result.get('restarts',0))
  stats['seconds']=time.perf_counter()-t;results.append(stats);print(json.dumps(stats),flush=True)
 output={'independent_seed':94557329,'all_original_models_and_every_learned_clause_checked':True,'results':results,'seconds':time.perf_counter()-start}
 (H/'solver_plus_independent_results.json').write_text(json.dumps(output,indent=2));print('ALL PASS')
if __name__=='__main__':main()

