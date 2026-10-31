"""Exact checks for imported/adapted global moments. No LP feasibility oracle."""
from pathlib import Path
from itertools import combinations
from math import comb
import json

def census(S,n):
 V=set(range(1<<n));S=set(S);deg={v:sum(v^(1<<d) in S for d in range(n)) for v in S};assert all(d<=2 for d in deg.values())
 counts=[0]*5
 for a,b in combinations(range(n),2):
  bits=(1<<a)|(1<<b)
  for root in V:
   if root&bits:continue
   F={root,root^(1<<a),root^(1<<b),root^bits};counts[len(F&S)]+=1
 if counts[4]:return None
 y=[sum(sum(v^(1<<d) in S for d in range(n))==k for v in V-S) for k in range(n+1)]
 todo=set(S);paths=0;isolates=sum(d==0 for d in deg.values())
 while todo:
  start=todo.pop();C={start};stack=[start]
  while stack:
   for d in range(n):
    w=stack[-1]^(1<<d)
    if w in todo:todo.remove(w);C.add(w);stack.append(w);break
   else:stack.pop()
  if any(deg[v]!=2 for v in C):paths+=1
 v=len(S);N=comb(n,2)*(1<<(n-2))
 assert sum(y)==(1<<n)-v
 assert sum(k*y[k] for k in range(n+1))==(n-2)*v+2*paths
 assert counts[3]==v-2*paths+isolates
 assert sum(comb(k,2)*y[k] for k in range(n+1))==(n*n-3*n+3)*v-2*N+(2*n-4)*paths+isolates+2*counts[0]
 assert y[0]<=4*counts[0]+isolates
 return True
checked=0
for mask in range(256):
 S={v for v in range(8) if mask>>v&1}
 if any(sum(v^(1<<d) in S for d in range(3))>2 for v in S):continue
 if census(S,3):checked+=1
v=236;F0=0;T=954;y={5:122,6:34,7:120}
assert sum(y.values())==512-v and sum(k*a for k,a in y.items())==7*v+2
assert sum(comb(k,2)*a for k,a in y.items())==57*v-9202+2*F0
assert T+2*F0==9214-35*v and T>=4*v+6
r={'Q3_square_free_degree_at_most_two_sets':checked,'exact_moments_and_y0_inequality_all_pass':True,'v236_integer_moment_witness':{'v':v,'Fempty':F0,'T':T,'y':y,'geometric_realization_claimed':False},'conclusion':'These moment equations and y0 bound alone do not exclude236 vertices.'}
Path(__file__).with_suffix('.json').write_text(json.dumps(r,indent=2));print(json.dumps(r,indent=2))
