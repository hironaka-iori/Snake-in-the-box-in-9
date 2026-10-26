"""Independently check saved forests, share values and every finite-model potential."""
from pathlib import Path
from fractions import Fraction
import collections,gzip,hashlib,itertools,json,sys
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/'work/solver_packages'));import numpy as np
pairs=list(itertools.combinations(range(9),2))
def sha(b):return hashlib.sha256(b).hexdigest()
def nb(v):return {v^(1<<d) for d in range(9)}
def alpha(S,v):return sum(not({v^(1<<a),v^(1<<b),v^(1<<a)^(1<<b)}&S) for a,b in pairs)
def shares(S,centres):
 out=[]
 for c in centres:
  total=0
  for q in nb(c):
   degree=len(nb(q)&S)
   empty=sum(not({q,q^(1<<a),q^(1<<b),q^(1<<a)^(1<<b)}&S) for a,b in pairs)
   total+=12*empty//degree if degree else 0
  out.append(total)
 return out
def forest(S,W):
 B={v for v in range(512) if min((v^c).bit_count() for c in W[1:-1])<=4}
 assert set(W)<=S<=B
 degree={v:len(nb(v)&S) for v in S};assert all(d<=2 for d in degree.values())
 inside=[v for v in S if nb(v)<=B];assert all(degree[v]>0 for v in inside)
 assert sum(degree[v]==1 for v in inside)<=2
 todo=set(S)
 while todo:
  seed=todo.pop();component={seed};queue=[seed]
  while queue:
   v=queue.pop()
   for w in nb(v)&todo:todo.remove(w);component.add(w);queue.append(w)
  assert sum(degree[v] for v in component)==2*(len(component)-1)
 return [alpha(S,v) for v in W[1:-1]]
