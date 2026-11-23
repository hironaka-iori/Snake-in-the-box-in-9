from pathlib import Path
import json,sys,collections,itertools
D=Path(__file__).resolve().parent
def complete(core,left,right,remain,budget=100000,cnf_only=False):
 A=set(core);ctr=collections.Counter(x^(1<<d) for x in A for d in range(9));N=0;cla=[];where=collections.defaultdict(dict);layers=[];endstage=[]
 def new():
  nonlocal N
  N+=1;return N
 def amo(ls):
  if len(ls)<=5:
   cla.extend([-a,-b] for a,b in itertools.combinations(ls,2));return
  prev=None
  for x in ls[:-1]:
   z=new();cla.append([-x,z])
   if prev:cla.extend(([-prev,z],[-x,-prev]))
   prev=z
  cla.append([-ls[-1],-prev])
 def gap(root,mask,kind):
  gi=len(layers);h=mask.bit_count()
  ranks=[{} for _ in range(1,min(max(h-1,0),remain if kind else h)+1)]
  delta=mask
  while delta:
   depth=delta.bit_count();x=root^delta
   if 1<=depth<=len(ranks) and x not in A and ctr[x]==int(depth==1)+int(not kind and h-depth==1):
    ranks[depth-1][x]=0
   delta=(delta-1)&mask
  prev={root}
  for layer in ranks:
   for x in list(layer):
    if not any((x^(1<<d)) in prev for d in range(9)):del layer[x]
   prev=layer
  if not kind:
   nex={root^mask}
   for layer in ranks[::-1]:
    for x in list(layer):
     if not any((x^(1<<d)) in nex for d in range(9)):del layer[x]
    nex=layer
  acts=[]
  for layer in ranks:
   for x in layer:
    k=new();layer[x]=k;where[x][gi]=k
   vals=list(layer.values());amo(vals)
   if kind:
    a=new();acts.append(a);cla.append([-a,*vals]);cla.extend([-k,a] for k in vals)
    if len(acts)>1:cla.append([-a,acts[-2]])
   else:cla.append(vals)
  for i in range(1,len(ranks)):
   for x,k in ranks[i].items():cla.append([-k,*[ranks[i-1][y] for d in range(9) if (y:=x^(1<<d)) in ranks[i-1]]])
  layers.append(ranks)
  if kind:endstage.append(acts)
 gap(core[0],left,True)
 for u,v in zip(core,core[1:]):gap(u,u^v,False)
 gap(core[-1],right,True)
 la,ra=endstage
 lens=[]
 for l in range(len(la)+1):
  r=remain-l
  if 0<=r<=len(ra):
   z=new();lens.append(z)
   for k,acts in ((l,la),(r,ra)):
    if k:cla.append([-z,acts[k-1]])
    if k<len(acts):cla.append([-z,-acts[k]])
 cla.append(lens)
 occ={}
 for x,vs in where.items():
  vals=list(vs.values());amo(vals)
  if len(vals)==1:occ[x]=vals[0]
  else:
   ox=new();occ[x]=ox;cla.extend([-k,ox] for k in vals)
 for x,gs in where.items():
  for d in range(9):
   y=x^(1<<d)
   if y<=x or y not in where:continue
   for g,k in gs.items():
    same=where[y].get(g)
    if same and len(where[y])==1:continue
    cla.append([-k,-occ[y]]+([same] if same else []))
 if cnf_only:return N,cla
 from pysat.solvers import Cadical195
 with Cadical195(bootstrap_with=cla) as s:
  s.conf_budget(budget);result=s.solve_limited();used=s.accum_stats()['conflicts']
  if not result:return ('UNSAT' if result is False else 'UNKNOWN',used,None)
  model=set(s.get_model());out=[]
  def picks(gi):return [x for layer in layers[gi] for x,k in layer.items() if k in model]
  out+=picks(0)[::-1];out.append(core[0])
  for i,v in enumerate(core[1:],1):out+=picks(i);out.append(v)
  out+=picks(len(layers)-1)
  assert len(out)==1+remain+sum((a^b).bit_count() for a,b in zip(core,core[1:]))
  assert len(set(out))==len(out) and all(((a^b).bit_count()==1)==(j==i+1) for i,a in enumerate(out) for j,b in enumerate(out) if j>i)
  return 'FOUND',used,out
if __name__=='__main__':
 source=sys.argv[1];budget=int(sys.argv[2]);cache={}
 for i,line in enumerate((D/source).read_text().splitlines()):
  row,d,t,a,j,l,r,n,np,*c=map(int,line.split());key=(tuple(c),l,r,n)
  if key not in cache:cache[key]=complete(c,l,r,n,budget)
  z,m,w=cache[key];print(json.dumps([i,z,m,w],separators=(',',':')),flush=True)
  if w:break
