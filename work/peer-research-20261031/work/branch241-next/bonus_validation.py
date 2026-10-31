from fractions import Fraction as F
from pathlib import Path
import json,itertools
count=0
for h in range(8):
 for n1 in range(h+1):
  for n2 in range(h-n1+1):
   n3=h-n1-n2;K=n1+2*n2+3*n3;V=4*n1+2*n2
   assert F((13-h)*K,3)+V<=42*(h>0)
   count+=1
cube_patterns=[]
for other in [None]+list(range(1,8)):
 S={0} if other is None else {0,other}
 q=0
 for d in range(3):
  for bit in (0,1):q+=all(v not in S for v in range(8) if (v>>d)&1==bit)
 distance=None if other is None else other.bit_count()
 assert q==(3 if other is None else 3-distance)
 cube_patterns.append({'other':other,'distance':distance,'empty_faces':q})
for h in range(1,8):
 for t in range(1,4):
  for r in range(3,7):
   rhs=F(2*(2*r+1-h),3*r*(r+1))+F(2*(r-3)*((t<=2)+3*(t==1)),3*r*(r+1))
   assert F(2,h*t)>=rhs
result={'per_empty_square_occupancy_distributions_checked':count,'singleton_two_point_patterns':cube_patterns,'all84_bonus_scalar_inequalities_checked':True,'C2_distance3_contributes_zero_empty_faces':True}
Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2));print(json.dumps(result,indent=2))
