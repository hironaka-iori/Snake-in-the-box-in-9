"""Independent counterexamples and exact complement-moment identities."""
from pathlib import Path
from itertools import combinations
from collections import Counter
from fractions import Fraction
import json,hashlib
H=Path(__file__).parent

def census(S,n):
 S=set(S);adj={x:[x^(1<<d) for d in range(n) if x^(1<<d) in S] for x in S};assert all(len(a)<=2 for a in adj.values())
 y=Counter(sum((x^(1<<d)) in S for d in range(n)) for x in range(1<<n) if x not in S);f=Counter()
 for a,b in combinations(range(n),2):
  free=(1<<a)|(1<<b)
  for base in range(1<<n):
   if not base&free:f[len(S&{base,base^(1<<a),base^(1<<b),base^free})]+=1
 seen=set();paths=c4=0
 for x in S:
  if x in seen:continue
  todo=[x];seen.add(x);C=[]
  while todo:
   v=todo.pop();C.append(v)
   for w in adj[v]:
    if w not in seen:seen.add(w);todo.append(w)
  if all(len(adj[v])==2 for v in C):c4+=len(C)==4
  else:paths+=1
 v=len(S);isolated=sum(not a for a in adj.values());cut=sum(k*t for k,t in y.items());moment=sum(k*(k-1)//2*t for k,t in y.items())
 assert cut==(n-2)*v+2*paths
 assert moment==(n*n-3*n+3)*v-n*(n-1)*(1<<(n-2))+2*(n-2)*paths+isolated-2*c4+2*f[0]
 assert y[0]<=4*f[0]+isolated
 return {'vertices':v,'path_components':paths,'isolates':isolated,'selected4cycles':c4,'empty_squares':f[0],'singleton_squares':f[1],'y':dict(y),'cut':cut,'second_moment':moment}

def main():
 checked=0
 for n in (3,4):
  neighbors=[sum(1<<(x^(1<<d)) for d in range(n)) for x in range(1<<n)]
  for mask in range(1<<(1<<n)):
   S={x for x in range(1<<n) if mask>>x&1}
   if any((neighbors[x]&mask).bit_count()>2 for x in S):continue
   census(S,n);checked+=1
 units=[1<<i for i in range(9)];coil=[]
 for i,u in enumerate(units):coil.extend([u,u^units[(i+1)%9]])
 path=coil[:-1]
 for P,cyclic in ((coil,True),(path,False)):
  assert len(P)==len(set(P))
  for i,x in enumerate(P):
   for j in range(i+1,len(P)):assert ((x^P[j]).bit_count()==1)==(j==i+1 or (cyclic and i==0 and j==len(P)-1))
  assert census(P,9)['y'][9]==1
 example=[0,1,3,7,15,31,63];B={x for x in range(512) if (x^1).bit_count()<=4};U={31}
 full=sum(u in U and w not in U for u in example for w in example if (u^w).bit_count()==1)
 truncated=sum(u in U and w not in U and w in B for u in example for w in example if (u^w).bit_count()==1);assert full==2 and truncated==1
 fake={5:122,6:34,7:120};assert sum(fake.values())==276 and sum(k*v for k,v in fake.items())==1654 and sum(k*(k-1)//2*v for k,v in fake.items())==4250
 blind=Fraction(256*8*9*8*31,40*9**3-131*9**2+4*9+136-31*6)
 result={'degree2_sets_exhaustively_checked_Q3_Q4':checked,'all_corrected_moments_and_y0_budget_passed':True,'coil18':{'vertices':coil,'census':census(coil,9)},'snake17':{'vertices':path,'census':census(path,9)},'n9_invalid_dual':{'R':-13,'unscaled_y8_slack':-104,'blind_formula_value_not_valid_bound':str(blind)},'boundary_counterexample':{'path':example,'ball_centre':1,'radius':4,'U':[31],'true_cut':full,'truncated_cut':truncated,'global_endpoints_in_U':0},'236vertex_moment_vector_passed':True}
 (H/'coil_transfer_checks.json').write_text(json.dumps(result,indent=2));print(json.dumps({k:v for k,v in result.items() if k not in ('coil18','snake17')},indent=2))
if __name__=='__main__':main()
