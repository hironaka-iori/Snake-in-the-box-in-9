from fractions import Fraction as F
from pathlib import Path
import json,itertools,math
H=Path(__file__).resolve().parent

def bound(p,d,R):return F(1098960*d+8*p+R,p+4200*d)
assert bound(480,1,578)==F(551689,2340)
assert bound(495,1,578)>235 and bound(496,1,578)<235
assert 227*496-111960-578==54
# Exact threshold equality does not exclude a 235-edge path.
p,d,R=112538,227,578*227
assert bound(p,d,R)==235
# Scaling a certificate requires scaling potential range too.
assert bound(480,1,578)==bound(960,2,1156)
# Elementary dual with overlapping four-vertex groups on K5.
V=set(range(5));groups=[V-{v} for v in V];weights=[F(1,4)]*5
coverage={v:sum(w for A,w in zip(groups,weights) if v in A) for v in V}
assert all(x<=1 for x in coverage.values());dual=sum(weights);assert dual==F(5,4)
checked=0
for mask in range(32):
 omitted={v for v in V if mask>>v&1}
 if all(len(omitted&A)>=1 for A in groups):assert len(omitted)>=dual;checked+=1
invalid=[F(1,3)]*5
assert any(sum(w for A,w in zip(groups,invalid) if v in A)>1 for v in V)
# Verify the periodic-word identity exhaustively on small coordinate alphabets.
period_cases=0
for period in range(2,9):
 for word in itertools.product(range(3),repeat=period):
  seq=(word+word)[:-1];x=0
  for a in seq:x^=1<<a
  assert x==1<<word[-1];period_cases+=1
out={'status':'PASS','conditional_formula_at_mu480':str(bound(480,1,578)),'conditional_integer_floor_mu480':bound(480,1,578).__floor__(),'strict_mu_threshold_d1_R578':str(F(112538,227)),'integer_mu_sufficient_d1_R578':496,'bound_at_mu495':str(bound(495,1,578)),'bound_at_mu496':str(bound(496,1,578)),'mu496_strict_margin_numerator':54,'threshold_equality_bound':235,'scale_invariance_requires_scaling_R':True,'overlap_dual_example':{'vertices':5,'groups':5,'weight_each':'1/4','coverage_each':'1','omission_lower_bound':'5/4','integer_omission_lower_bound':2,'disjoint_groups_max':1,'feasible_omission_sets_checked':checked,'invalid_1over3_weights_rejected':True},'period_word_identity_cases':period_cases,'scope':'arithmetic conditional on supplied global formula; no full arbitrary-snake bridge verified'}
(H/'aggregate_review_checks.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
