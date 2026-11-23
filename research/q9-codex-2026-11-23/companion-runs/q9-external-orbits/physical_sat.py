from pathlib import Path
from itertools import combinations
from random import Random
from collections import Counter
from pysat.solvers import Minicard
from setup import read,check,flaws
import sys,time
r=Path(__file__).resolve().parent
def subgroup(support):
 a=support[0];g=[0]
 for b in support[1:]:g += [x^(1<<a)^(1<<b) for x in g]
 return g
def solve(p,axes,budget):
 # Constraint graph: exactly one value per time, at most one visit per vertex.
 # Consecutive choices must touch. Occupied vertices have degree at most two,
 # and the two endpoints have degree at most one, excluding every chord.
 delta=subgroup(axes);layers=[];n=len(p);occ=[[] for _ in range(512)];var=512
 with Minicard() as s:
  for i,x in enumerate(p):
   layer={}
   for m in ([0] if i==0 else delta):
    v=x^m;var+=1;layer[v]=var;occ[v].append(var);s.add_clause([-var,v+1])
   layers.append(layer);vs=list(layer.values());s.add_clause(vs);s.add_atmost(vs,1)
  for x,ls in enumerate(occ):
   if not ls:s.add_clause([-x-1]);continue
   s.add_clause([-x-1,*ls]);s.add_atmost(ls,1)
   nb=[(x^(1<<d))+1 for d in range(9) if occ[x^(1<<d)]]
   if len(nb)>2:
    # A fresh proxy equals true iff the vertex is vacant and therefore may relax degree.
    for a,b,c in combinations(nb,3):s.add_clause([-x-1,-a,-b,-c])
  for i,L in enumerate(layers[:-1]):
   nxt=layers[i+1]
   for x,v in L.items():s.add_clause([-v,*[nxt[y] for d in range(9) if (y:=x^(1<<d)) in nxt]])
  for L in (layers[0],layers[-1]):
   for x,var0 in L.items():
    for a,b in combinations([(x^(1<<d))+1 for d in range(9) if occ[x^(1<<d)]],2):s.add_clause([-var0,-a,-b])
  s.set_phases([L[x] for L,x in zip(layers,p)]);s.conf_budget(budget);u=s.solve_limited()
  if u is None:return '?',None
  if not u:return 'U',None
  vals=set(s.get_model());out=[next(x for x,v in L.items() if v in vals) for L in layers];return 'F',out
def main():
 ctrl=int(sys.argv[1]);secs=int(sys.argv[2]);rng=Random(991832);ps=read(r/('truth.pts' if ctrl else 'walks.pts'));counts=Counter();start=time.monotonic()
 for t in range(1000):
  axes=rng.sample(range(9),3+(t%3) if ctrl else 5+(t//len(ps))%2);i=t%len(ps);p=ps[i].copy()
  if ctrl:
   # Ends remain unperturbed so the first layer is a valid symmetry normalization.
   D=subgroup(axes);m1=D[1];m2=D[2];q=[x^(m1 if 17<=j<44 else m2 if 67<=j<98 else m1^m2 if 115<=j<153 else 0) for j,x in enumerate(p)]
   assert flaws(q);p=q
  status,out=solve(p,axes,5000 if ctrl else 3000);counts[status]+=1
  if out:
   check(out,191 if ctrl else 192);print(i,t,*out,flush=True)
   if not ctrl:break
  if (ctrl and t+1==len(ps)) or time.monotonic()-start>=secs:break
 print(dict(counts),file=sys.stderr)
if __name__=='__main__':main()

