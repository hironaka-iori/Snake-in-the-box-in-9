from pathlib import Path
from itertools import combinations
from fractions import Fraction
from math import lcm,gcd
import json
HERE=Path(__file__).resolve().parent

def snake(h,sizes):
 assert len(sizes)==h and 1<=h<=7
 out=[];heavy=0
 for i,t in enumerate(sizes):
  outer=1<<(i+2)
  # The Q2 fibre path starts at incoming heavy value and flips0 then1.
  pts=[heavy]
  for d in range(t-1):pts.append(pts[-1]^(1<<d))
  out.extend(outer+x for x in pts);heavy=pts[-1]
  if i<h-1:out.append(outer+(1<<(i+3))+heavy)
 return out

def verify(p):
 assert len(set(p))==len(p)
 for i,x in enumerate(p):
  for j in range(i+1,len(p)):assert ((x^p[j]).bit_count()==1)==(j==i+1)

def root_score(S,x):
 alpha=0
 for a,b in combinations(range(9),2):
  if all((x^m) not in S for m in (1<<a,1<<b,(1<<a)|(1<<b))):alpha+=1
 adaptive=Fraction(alpha);uniform=Fraction(alpha);terms=[]
 for j in range(9):
  for a,b in combinations([k for k in range(9) if k!=j],2):
   f=[x^(1<<j)^m for m in (0,1<<a,1<<b,(1<<a)|(1<<b))]
   if any(v in S for v in f):continue
   ts=[sum((v^(1<<k)) in S for v in f) for k in range(9) if k not in (a,b)]
   h=sum(t>0 for t in ts);t=sum((v^(1<<j)) in S for v in f)
   assert h>=1 and 1<=t<=3
   adaptive+=Fraction(2,h*t);uniform+=Fraction(2,7*t);terms.append([h,t])
 e2=len(terms);d=sum(7-h for h,t in terms);assert d%3==0;e3=d//3
 independent_e3=0
 for j in range(9):
  for ds in combinations([k for k in range(9) if k!=j],3):
   pts=[x^(1<<j)]
   for k in ds:pts += [v^(1<<k) for v in pts]
   independent_e3+=all(v not in S for v in pts)
 assert e3==independent_e3
 lower=Fraction(alpha)+Fraction(2*e2+e3,21)
 assert adaptive>=lower
 c1=c21=c22=0
 for ds in combinations(range(9),3):
  pts=[x]
  for k in ds:pts += [v^(1<<k) for v in pts]
  chosen=[v for v in pts if v in S]
  if len(chosen)==1:c1+=1
  elif len(chosen)==2:
   distance=(chosen[0]^chosen[1]).bit_count()
   c21+=(distance==1);c22+=(distance==2)
 assert sum(t==1 for h,t in terms)==3*c1
 assert sum(t<=2 for h,t in terms)==3*c1+2*c21+c22
 stronger=Fraction(alpha)+Fraction(2*e2+e3+12*c1+2*c21+c22,21)
 assert adaptive>=stronger
 for r in range(1,7):
  lower_r=Fraction(alpha)+Fraction(2*((2*r-6)*e2+3*e3),3*r*(r+1))
  assert adaptive>=lower_r
 return alpha,adaptive,uniform,terms

def main():
 patterns=[(h,[t]*h) for h in range(1,8) for t in range(1,4)]+[(4,[2,3,3,3]),(4,[3,2,3,3])]
 scale=1;uniformscale=1;cases=[];denom_witness={}
 root_checks=0
 for h,sizes in patterns:
  p=snake(h,sizes);verify(p);S=set(p);F={0,1,2,3}
  fibre=[sum((v^(1<<k)) in S for v in F) for k in range(2,9)]
  assert sum(v>0 for v in fibre)==h and fibre[:h]==sizes
  for i,x in enumerate(p):
   alpha,a,g,terms=root_score(S,x);root_checks+=1;scale=lcm(scale,a.denominator);uniformscale=lcm(uniformscale,g.denominator)
   assert (1260*a).denominator==1 and (21*g).denominator==1
   denom_witness.setdefault(a.denominator,{'h':h,'sizes':sizes,'root_index':i,'root':x,'alpha':alpha,'adaptive':str(a),'uniform':str(g),'vertices':p})
  cases.append({'h':h,'sizes':sizes,'vertices':len(p),'induced_path_verified':True})
 coeffscale=lcm(*(Fraction(2,h*t).denominator for h in range(1,8) for t in range(1,4)))
 explicit=[]
 for path,root,expected in [(snake(4,[2,3,3,3]),18,'36421/180'),(snake(7,[3]*7),10,'42611/315')]:
  alpha,av,gv,ts=root_score(set(path),root);assert str(av)==expected
  explicit.append({'vertices':path,'root':root,'alpha':alpha,'adaptive':str(av),'uniform':str(gv)})
 result={'explicit_minimum_scale_witnesses':explicit,'root_bound_checks':root_checks,'all_21_h_t_pairs_realized_by_induced_paths':True,'stronger21_occupancy_bonus_all_roots_checked':True,'individual_coefficient_minimum_scale':coeffscale,'full_pointwise_adaptive_scale_required_by_examples':scale,'uniform_scale_required_by_examples':uniformscale,'cases':cases,'pointwise_denominator_witnesses':denom_witness,'no_numeric_upper_bound_claimed':True}
 (HERE/'local_coefficients.json').write_text(json.dumps(result,indent=2));print(json.dumps({k:v for k,v in result.items() if k!='pointwise_denominator_witnesses'},indent=2));print('DENOMINATORS',sorted(denom_witness))
if __name__=='__main__':main()
