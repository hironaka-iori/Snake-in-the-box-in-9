from pathlib import Path
from itertools import combinations
from collections import defaultdict,Counter
from random import Random
from pysat.solvers import Minicard
import sys
from prep import valid
r=Path(__file__).resolve().parent
def dom(p,win,active):
 n=len(p);D=[{x} for x in p];moves=[x^y for x,y in zip(p,p[1:])]
 for l in range(n-1):
  mask=0
  for h in range(l+1,min(n,l+win+1)):
   a=moves[h-1]
   if a.bit_count()!=1 or mask&a:break
   mask|=a
   if h<l+2 or not any(l<i<h for i in active):continue
   v=mask
   while v:
    i=l+v.bit_count()
    if i<h and i in active:D[i].add(p[l]^v)
    v=(v-1)&mask
 return D
def solve(p,win,active,budget):
 D=dom(p,win,active);n=len(p)
 # Release both ends and choose one further vertex at each tip. In this model
 # they are free subject only to the exact global induced-path constraints.
 for j in (0,n-1):
  step=1 if j==0 else -1
  i=j+step
  D[i]|={x^(1<<d) for x in D[j+2*step] for d in range(9)}
  D[j]|={x^(1<<d) for x in D[i] for d in range(9)}
 idx=defaultdict(list);lit=[];cnt=0
 fixed={v:i for i,ds in enumerate(D) if len(ds)==1 for v in ds}
 # Remove domains that already conflict with a fixed non-neighbor.
 for i,ds in enumerate(D):
  D[i]={v for v in ds if all(abs(i-fixed[y])<=1 and (v!=y or i==fixed[y]) for y in [v]+[v^(1<<d) for d in range(9)] if y in fixed)}
  if not D[i]:return 'U',None
 with Minicard() as sat:
  for i,ds in enumerate(D):
   w={}
   for v in ds:
    cnt+=1;w[v]=cnt;idx[v].append((i,cnt))
   choices=list(w.values());sat.add_clause(choices);sat.add_atmost(choices,1);lit.append(w)
  for i,w in enumerate(lit):
   for v,vi in w.items():
    if i+1<n:sat.add_clause([-vi]+[lit[i+1][y] for d in range(9) if (y:=v^(1<<d)) in lit[i+1]])
    for y in [v]+[v^(1<<d) for d in range(9)]:
     for j,uj in idx[y]:
      if j+1<i:sat.add_clause([-vi,-uj])
  sat.set_phases([w[x] for w,x in zip(lit,p) if x in w]);sat.conf_budget(budget);res=sat.solve_limited()
  if res is not True:return ('U' if res is False else '?'),None
  model=set(sat.get_model());out=[next(v for v,t in w.items() if t in model) for w in lit];assert valid(out);return 'F',out
def main():
 name,limit,win,budget=sys.argv[1:];limit=int(limit);win=int(win);budget=int(budget);rng=Random(763199);rows=[list(map(int,s.split())) for s in (r/(name+'.pts')).read_text().splitlines()]
 inds=list(range(len(rows)));rng.shuffle(inds);counts=Counter()
 for j in inds[:limit]:
  p=rows[j];n=len(p);active=set()
  if name=='geocontrol':active=set(range(n))
  else:
   flaws=[(i,k) for i in range(n) for k in range(i+2,n) if (p[i]^p[k]).bit_count()<=1]
   centers={q for pair in flaws for q in pair};close=[i for i,v in enumerate(p) if any((v^p[q]).bit_count()<=2 for q in centers)]
   centers.update(rng.sample(close,min(7,len(close))));centers.update(rng.sample(range(n),4))
   for q in centers:active.update(range(max(0,q-8),min(n,q+9)))
  status,out=solve(p,win,active,budget);counts[status]+=1
  if out:
   print(j,0,*out,flush=True)
   if name!='geocontrol':break
 print(dict(counts),file=sys.stderr)
if __name__=='__main__':main()

