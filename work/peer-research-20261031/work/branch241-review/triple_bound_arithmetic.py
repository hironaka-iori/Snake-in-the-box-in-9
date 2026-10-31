"""Exact sufficient thresholds; no assertion that any window threshold is true."""
from pathlib import Path
from fractions import Fraction
from collections import Counter
from itertools import product
import json,re,sys
R=Path(__file__).resolve().parent;sys.path.insert(0,str(R))
from independent_global_snake import validate
from independent_encoding_review import direct,Geometry

def gap(v,T,single=22,endpoint=8):
 k,r=divmod(v-2,3)
 return Fraction(T*k+single*r,21)+endpoint-(9214-35*v)

def minimum_threshold(v):
 return next(t for t in range(1,10000) if gap(v,t)>0)

def canonical(ds):
 seen={};return tuple(seen.setdefault(d,len(seen)) for d in ds)

def main():
 shapes=Counter()
 for ds in product(range(9),repeat=4):
  p=[0]
  for d in ds:p.append(p[-1]^(1<<d))
  if len(set(p))!=5:continue
  if any(((p[i]^p[j]).bit_count()==1)!=(j-i==1) for i in range(5) for j in range(i+1,5)):continue
  shapes[canonical(ds)]+=1
 assert set(shapes)=={(0,1,2,0),(0,1,2,3)}
 outcomes=[]
 for T,v in [(255,236),(267,235),(268,235)]:
  assert all(gap(w,T)>0 for w in range(v,513))
  increments=[735+22,735+T-44];assert min(increments)>0
  outcomes.append({'assumed_triple_threshold':T,'excluded_vertices_from':v,'conditional_max_edges':v-2,'critical_gap':str(gap(v,T)),'minimum_sufficient_integer_T_at_critical_v':minimum_threshold(v),'all_v_through_512_checked':True,'scaled_gap_increments_by_remainder':increments})
 repo=R.parent/'branch241-audit/repo';f=repo/'work/spectral/stronger/EndpointFourWitness.lean';source=f.read_text(encoding='utf-8');nums=[int(v) for v in re.search(r'def values.*?#\[(.*?)\]',source,re.S).group(1).split(',')];validate(nums,nums[:3]);alpha=direct(Geometry(9),set(nums),nums[0])[0];assert alpha==4
 result={'status':'CONDITIONAL arithmetic only; triple inequalities are unproved until both shape queries are certified','canonical_three_centre_shapes':{''.join(map(str,k)):v for k,v in shapes.items()},'conditional_implications':outcomes,'endpoint_sharpness_witness':{'source':str(f),'vertices':len(nums),'all_pair_induced_path_check':True,'initial_endpoint_alpha':alpha},'endpoint_theorem_source':'work/spectral/stronger/UpperBound247.lean: endpoint_alpha_ge_four; premise 1<=m and endpoint index','important_correction':'267, rather than 268, suffices for max_edges233 when the existing single-centre22 bound is included.'}
 (R/'triple_bound_arithmetic.json').write_text(json.dumps(result,indent=2));print(json.dumps(result,indent=2))
if __name__=='__main__':main()
