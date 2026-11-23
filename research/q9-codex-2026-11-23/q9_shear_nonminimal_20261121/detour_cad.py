from pathlib import Path
import collections,itertools,json,sys
from pysat.solvers import Cadical195
from pysat.card import CardEnc,EncType
D=Path(__file__).resolve().parent
N=[{x^(1<<d) for d in range(9)} for x in range(512)]
def sections(x,mask):
 ranks=[set() for i in range(mask.bit_count()+1)]
 z=mask
 while 1:
  ranks[z.bit_count()].add(x^z)
  if not z:break
  z=(z-1)&mask
 return ranks
def solve(c,L,R,l,r,detours,budget=5000):
 assert 1<=len(detours)<=2 and all(i in range(len(c)-1) and (c[i]^c[i+1]).bit_count()>=2 and k in (2,4) for i,k in detours.items())
 layer=sections(c[0],L)[1:l+1][::-1]+[{c[0]}]
 for i,(a,b) in enumerate(zip(c,c[1:])):
  h=(a^b).bit_count()+detours.get(i,0)
  if i not in detours:layer+=sections(a,a^b)[1:];continue
  for t in range(1,h):
   layer.append({v for v in range(512) if (dd:=(v^a).bit_count())<=t and (t-dd)%2==0 and (v^b).bit_count()<=h-t})
  layer.append({b})
 layer+=sections(c[-1],R)[1:r+1];n=len(layer);fixed={i:z.pop() for i,s in enumerate(layer) if len(z:=s.copy())==1};sent={}
 while 1:
  for i,v in fixed.items():
   if i in sent:continue
   sent[i]=v
   for j,s in enumerate(layer):
    if j==i:continue
    if abs(j-i)==1:s.intersection_update(N[v])
    else:s.difference_update(N[v]);s.discard(v)
    if not s:return 'PROP',None
  old=sum(map(len,layer))
  for ix in (range(1,n),range(n-2,-1,-1)):
   reverse=ix.step<0
   for j in ix:
    prev=layer[j+1 if reverse else j-1];z=layer[j]
    z.difference_update([v for v in z if N[v].isdisjoint(prev)])
    if not z:return 'PROP',None
  fixed={i:next(iter(z)) for i,z in enumerate(layer) if len(z)==1}
  if len(fixed)==len(sent) and old==sum(map(len,layer)):break
 counter=0;var=[];uses=collections.defaultdict(list);cla=[]
 for z in layer:
  local={}
  for x in z:
   counter+=1;local[x]=counter;uses[x].append(counter)
  var.append(local);cla.append(list(local.values()))
 occ={}
 for x,lits in uses.items():
  if len(lits)==1:occ[x]=lits[0]
  else:
   counter+=1;occ[x]=counter
   cla.extend([ -v,counter] for v in lits)
 for i,vs in enumerate(var):
  for x,k in vs.items():
   for y in N[x]&occ.keys():
    clause=[-k,-occ[y]]
    if i and y in var[i-1]:clause.append(var[i-1][y])
    if i+1<n and y in var[i+1]:clause.append(var[i+1][y])
    cla.append(clause)
   if i:cla.append([-k,*[var[i-1][y] for y in N[x]&var[i-1].keys()]])
 for lits in [*uses.values(),*[list(z.values()) for z in var]]:
  if len(lits)<=1:continue
  card=CardEnc.atmost(lits,1,top_id=counter,encoding=EncType.seqcounter)
  counter=max(counter,card.nv);cla+=card.clauses
 for x,values in uses.items():
  if len(values)>1:cla.append([-occ[x],*values])
  nb=[occ[y] for y in N[x] if y in occ]
  for t in itertools.combinations(nb,3):cla.append([-occ[x],*[-v for v in t]])
  ep=[local[x] for local in (var[0],var[-1]) if x in local]
  for t in itertools.combinations(nb,max(0,len(nb)-1)):cla.append([-occ[x],*ep,*t])
 for x in occ:
  for a,b in itertools.combinations(range(9),2):
   m=(1<<a)|(1<<b)
   if x&m:continue
   square=[x,x^(1<<a),x^(1<<b),x^m]
   if all(z in occ for z in square):cla.append([-occ[z] for z in square])
 with Cadical195(bootstrap_with=cla) as sol:
  sol.conf_budget(budget);res=sol.solve_limited()
  if res is not True:return ('UNSAT' if res is False else 'UNKNOWN'),None
  model=set(sol.get_model());path=[next(x for x,k in vs.items() if k in model) for vs in var]
  assert len(set(path))==n and all((dist:=((x^y).bit_count()))!=0 and (dist==1)==(j==i+1) for i,x in enumerate(path) for j,y in enumerate(path) if j>i)
  return 'FOUND',path
