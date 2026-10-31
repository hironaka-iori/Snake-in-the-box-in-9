import itertools,random,json,time
from pathlib import Path
from solver import Solver
from rup_check import check
import solver as module

def brute(cs,n):
 return any(all(any(bool(bits>>(abs(l)-1)&1)==(l>0) for l in c) for c in cs) for bits in range(1<<n))
def verify(cs,s,r):
 if r['status']=='UNSAT':return check(cs,s.proof)
 assert r['status']=='SAT'
 a={abs(l):l>0 for l in r['model']};assert all(any(a[abs(l)]==(l>0) for l in c) for c in cs)
 return {}
def run():
 rng=random.Random(77122026);start=time.perf_counter();stats={'nontrivial_random_cases':0,'SAT':0,'UNSAT':0,'RUP_steps':0}
 for case in range(2400):
  n=rng.randrange(3,10);cs=[]
  for _ in range(rng.randrange(n,6*n+1)):
   vs=rng.sample(range(1,n+1),rng.choice((2,3)));cs.append([v*rng.choice((-1,1)) for v in vs])
  expected=brute(cs,n);s=Solver(cs,n);r=s.solve(3)
  assert (r['status']=='SAT')==expected,(case,cs,r)
  ck=verify(cs,s,r);stats['RUP_steps']+=ck.get('RUP_steps_checked',0);stats[r['status']]+=1;stats['nontrivial_random_cases']+=1
 holes=6;pigeons=7;v=lambda p,h:p*holes+h+1
 cs=[[v(p,h) for h in range(holes)] for p in range(pigeons)]+[[-v(p,h),-v(q,h)] for h in range(holes) for p in range(pigeons) for q in range(p+1,pigeons)]
 s=Solver(cs);r=s.solve(10);verify(cs,s,r);stats['PHP_7_into_6']={**r,'independent_check':check(cs,s.proof)}
 # Force a timeout exactly at the in-propagation deadline checkpoint, then resume.
 s=Solver(cs);real=module.time.perf_counter;calls=[0]
 def fake():
  calls[0]+=1
  return 2.0 if s.inspections>=8192 else 0.0
 module.time.perf_counter=fake
 try:r=s.solve(1)
 finally:module.time.perf_counter=real
 assert r['status']=='UNKNOWN'
 try:s.solve(10)
 except ValueError:resume_rejected=True
 else:resume_rejected=False
 assert resume_rejected
 r2={'status':'UNKNOWN','unsafe_resume_rejected':True}
 stats['forced_midpropagation_timeout_resume']=r2
 stats['seconds']=time.perf_counter()-start
 (Path(__file__).parent/'solver_adversarial_results.json').write_text(json.dumps(stats,indent=2));print(json.dumps(stats,indent=2))
if __name__=='__main__':run()

