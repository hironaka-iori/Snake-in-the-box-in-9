import itertools,json,random,time
from pathlib import Path
from solver import Solver
from rup_check import check
R=Path(__file__).resolve().parent;rng=random.Random(241234235);stats={'random_cases':0,'UNSAT':0,'SAT':0,'hint_steps':0,'hint_literals':0};start=time.perf_counter()
def brute(cs,n):
 for bits in range(1<<n):
  if all(any(bool(bits>>(abs(l)-1)&1)==(l>0) for l in c) for c in cs):return True
 return False
for i in range(1800):
 n=rng.randrange(1,9);cs=[]
 for _ in range(rng.randrange(0,45)):
  cs.append([rng.choice((-1,1))*rng.randrange(1,n+1) for _ in range(rng.randrange(0,6))])
 expected=brute(cs,n);s=Solver(cs,n);result=s.solve(seconds=2);assert (result['status']=='SAT')==expected,(cs,result)
 assert result['status']!='UNKNOWN'
 if expected:
  a={abs(l):l>0 for l in result['model']};assert all(any(a[abs(l)]==(l>0) for l in c) for c in cs)
 else:
  checked=check(cs,s.proof);stats['hint_steps']+=checked['RUP_steps_checked'];stats['hint_literals']+=checked['unit_hints_checked']
 stats[result['status']]+=1;stats['random_cases']+=1
hard=[]
for holes in (3,4,5):
 pigeons=holes+1;v=lambda p,h:p*holes+h+1;cs=[[v(p,h) for h in range(holes)] for p in range(pigeons)]
 cs += [[-v(p,h),-v(q,h)] for h in range(holes) for p in range(pigeons) for q in range(p+1,pigeons)]
 s=Solver(cs);r=s.solve(seconds=10);assert r['status']=='UNSAT';r['check']=check(cs,s.proof);hard.append(r)
 rejected=0
 for bad in ([{'clause':[],'hints':[len(cs)+999]}],[{'clause':[],'hints':[]}],[{'clause':[],'hints':[1]}]):
  try:check(cs,bad)
  except ValueError:rejected+=1
 assert rejected==3
stats['pigeonhole']=hard;stats['seconds']=time.perf_counter()-start;(R/'solver_tests.json').write_text(json.dumps(stats,indent=2));print(json.dumps(stats,indent=2))
