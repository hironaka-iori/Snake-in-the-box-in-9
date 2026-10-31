from pathlib import Path
import random,itertools,json,time
from solver_reduced import Solver
from rup_check import check
H=Path(__file__).parent;rng=random.Random(5173648254);rows=[];start=time.perf_counter();totalsteps=totalinactive=0

def oracle(cs,n):return any(all(any(bool(b>>(abs(l)-1)&1)==(l>0) for l in c) for c in cs) for b in range(1<<n))
def audit(s):
 for a in s.deactivation_audit:
  assert not set(a['ids_zero_based'])&set(a['locked_at_reduction'])
  assert not set(a['ids_zero_based'])&set(a['excluded'])
  assert all(i>=s.reducible_from and len(s.clauses[i])>2 for i in a['ids_zero_based'])
for variant in ({'binary':True,'minimize':True,'restart':'lbd'},{'binary':False,'circular':True,'restart':'luby'}):
 for _ in range(200):
  n=rng.randrange(3,10);cs=[[v*rng.choice((-1,1)) for v in rng.sample(range(1,n+1),rng.choice((2,3)))] for j in range(rng.randrange(n*2,n*7))]
  good=oracle(cs,n);s=Solver(cs,reduction_interval=2,min_candidates=2,keep_fraction=.3,**variant);r=s.solve(seconds=5)
  assert r['status'] in ('SAT','UNSAT') and (r['status']=='SAT')==good
  ck=check(cs,s.proof,require_empty=not good);totalsteps+=ck['RUP_steps_checked'];totalinactive+=len(s.inactive);audit(s)
  if good:
   m=set(r['model']);assert all(any(l in m for l in c) for c in cs)
# An exact RUP prefix: resolution of the first two static axioms, plus weakenings.
cs=[[1,2,3],[-1,4,5]];prefix=[{'clause':[2,3,4,5]+([v] if v else []),'hints':[1,2]} for v in [0,6,7,8,9,10]]
s=Solver(cs,prefix,reduction_interval=2,min_candidates=2,nvars=10)
# Synthetic lock tests only the protection policy; restore before logical search.
s.values[2]=1;s.reasons[2]=2;s.reduce_database();assert 2 not in s.inactive and len(s.inactive)>0;s.values[2]=0;s.reasons[2]=-1
r=s.solve();assert r['status']=='SAT';check(cs,prefix+s.proof,require_empty=False);audit(s);totalinactive+=len(s.inactive)
try:Solver([[1,2]],[{'clause':[],'hints':[1]}])
except ValueError:bad_prefix_rejected=True
else:bad_prefix_rejected=False
assert bad_prefix_rejected
for holes in (4,5):
 v=lambda p,h:p*holes+h+1;cs=[[v(p,h) for h in range(holes)] for p in range(holes+1)]+[[-v(p,h),-v(q,h)] for h in range(holes) for p in range(holes+1) for q in range(p+1,holes+1)]
 s=Solver(cs,reduction_interval=10,min_candidates=4,keep_fraction=.5,binary=True,minimize=True);r=s.solve(seconds=10);assert r['status']=='UNSAT';ck=check(cs,s.proof);audit(s);r['proof']=ck;rows.append(r);totalinactive+=len(s.inactive)
assert totalinactive>0
result={'random_cases':400,'all_SAT_original_models_and_all_RUP_checked':True,'bad_prefix_rejected':bad_prefix_rejected,'static_binary_locked_and_conflict_protection_audited':True,'deactivated_across_tests':totalinactive,'random_RUP_steps':totalsteps,'PHP':rows,'seconds':time.perf_counter()-start}
(H/'solver_reduced_tests.json').write_text(json.dumps(result,indent=2));print(json.dumps(result,indent=2))
