import json
from pathlib import Path
import solver_plus as M
from rup_check import check
H=Path(__file__).parent
s=M.Solver([[1,v] for v in range(2,9001)],binary=True)
real=M.time.perf_counter
M.time.perf_counter=lambda:2.0 if s.binary_visits>=8192 else 0.0
try:r=s.solve(seconds=1)
finally:M.time.perf_counter=real
assert r['status']=='UNKNOWN' and s.binary_visits==8192
try:s.solve()
except ValueError:reuse_rejected=True
else:reuse_rejected=False
assert reuse_rejected;check([[1,v] for v in range(2,9001)],s.proof,require_empty=False)
holes=5;v=lambda p,h:p*holes+h+1
cs=[[v(p,h) for h in range(holes)] for p in range(holes+1)]+[[-v(p,h),-v(q,h)] for h in range(holes) for p in range(holes+1) for q in range(p+1,holes+1)]
s=M.Solver(cs,binary=True,minimize=True,circular=True);q=s.solve(max_conflicts=1);assert q['status']=='UNKNOWN';verified=check(cs,s.proof,require_empty=False)
out={'binary_mid_edge_timeout_status':r['status'],'binary_visits_at_timeout':8192,'reuse_rejected':reuse_rejected,'conflict_budget_unknown_proof':verified}
(H/'solver_plus_timeout_results.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
