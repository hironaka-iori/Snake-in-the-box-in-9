from pathlib import Path
import collections,itertools,json,sys
from pysat.solvers import Minicard
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
def solve(c,L,R,l,r):
 layer=sections(c[0],L)[1:l+1][::-1]+[{c[0]}]
 for a,b in zip(c,c[1:]):layer+=sections(a,a^b)[1:]
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
 with Minicard(bootstrap_with=cla) as sol:
  for group in [*uses.values(),*[list(z.values()) for z in var]]:
   if len(group)>1:sol.add_atmost(group,1)
  sol.conf_budget(200000);res=sol.solve_limited()
  if res is not True:return ('UNSAT' if res is False else 'UNKNOWN'),None
  model=set(sol.get_model());path=[next(x for x,k in vs.items() if k in model) for vs in var]
  assert len(set(path))==n and all((dist:=((x^y).bit_count()))!=0 and (dist==1)==(j==i+1) for i,x in enumerate(path) for j,y in enumerate(path) if j>i)
  return 'FOUND',path
def main():
 mode=sys.argv[1]
 if mode=='control':
  from complete import complete
  for i,line in enumerate((D/'control.work').read_text().splitlines()):
   row,d,t,a,j,L,R,rem,np,*c=map(int,line.split())
   if rem<=max(L.bit_count()-1,R.bit_count()-1) or sum((v^w).bit_count()>1 for v,w in zip(c,c[1:]))<2:continue
   s,_,q=complete(c,L,R,rem)
   if q:
    l=q.index(c[0]);r=rem-l;st,p=solve(c,L,R,l,r);assert st=='FOUND' and p and l*r>0
    print(json.dumps([i,row,d,t,a,j,L,R,rem,l,r,c,q,p]));return
  raise RuntimeError('no planted sample')
 for fn in sys.argv[1:]:
  for i,line in enumerate((D/(fn+'.work')).read_text().splitlines()):
   row,d,t,a,j,L,R,rem,np,*c=map(int,line.split());stats={}
   for l in range(max(0,rem-max(R.bit_count()-1,0)),min(rem,max(L.bit_count()-1,0))+1):
    r=rem-l;st,q=solve(c,L,R,l,r);stats[l]=st
    if q:
     print(json.dumps([fn,i,stats,q]),flush=True);return
   print(json.dumps([fn,i,stats,None],separators=(',',':')),flush=True)
if __name__=='__main__':main()
