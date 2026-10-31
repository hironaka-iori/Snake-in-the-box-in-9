from fractions import Fraction as F
from pathlib import Path
import json
out=[]
A=[840//(r*(r+1)) for r in range(1,7)]
B=[420//(r*(r+1)) for r in range(1,7)]
C=[1260//(r*(r+1)) for r in range(1,7)]
for h in range(1,8):
 for t in range(1,4):
  weight=2520//(h*t);assert F(2520,h*t)==weight
  expr=120+60*(t<=2)+180*(t==1)
  for r in range(1,7):expr+=(h<=r)*(A[r-1]+B[r-1]*(t<=2)+C[r-1]*(t==1))
  assert expr==weight
  for r in range(1,7):assert F(2,h*t)>=F(2*(2*r+1-h),3*r*(r+1))
  out.append({'h':h,'t':t,'integer_weight':weight})
result={'all21_coefficients':out,'discrete_lower_bound_126_checks':True,'positive_threshold_expansion_21_checks':True,'A':A,'B':B,'C':C}
Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2));print(json.dumps(result,indent=2))
