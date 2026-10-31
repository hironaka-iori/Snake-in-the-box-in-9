import json,random,itertools,time
from pathlib import Path
from solver import Solver
from rup_check import check
rng=random.Random(98241234);records=[];sat=unsat=steps=0;start=time.perf_counter()
for case in range(1200):
 n=rng.randrange(3,11);cs=[[rng.choice((-1,1))*v for v in rng.sample(range(1,n+1),3)] for _ in range(rng.randrange(n,8*n+1))]
 expected=any(all(any(bool(bits>>(abs(l)-1)&1)==(l>0) for l in c) for c in cs) for bits in range(1<<n))
 s=Solver(cs,n);r=s.solve(seconds=2);assert r['status']==('SAT' if expected else 'UNSAT')
 if expected:sat+=1
 else:unsat+=1;steps+=check(cs,s.proof)['RUP_steps_checked']
 if r['conflicts']:records.append(r['conflicts'])
result={'nontrivial_random_3SAT_cases':1200,'SAT':sat,'UNSAT':unsat,'RUP_steps_checked':steps,'cases_with_conflicts':len(records),'max_conflicts':max(records),'seconds':time.perf_counter()-start};Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2));print(json.dumps(result,indent=2))
