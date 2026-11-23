from pathlib import Path
import json,sys,collections,itertools
D=Path(__file__).resolve().parent
def encoding(core,left,right,remain):
 gates={}
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
  gate=None
  if not kind and ranks:
   gate=new();gates[gi-1]=gate
  acts=[]
  for layer in ranks:
   for x in layer:
    k=new();layer[x]=k;where[x][gi]=k
   vals=list(layer.values());amo(vals)
   if kind:
    a=new();acts.append(a);cla.append([-a,*vals]);cla.extend([-k,a] for k in vals)
    if len(acts)>1:cla.append([-a,acts[-2]])
   else:cla.append([gate,*vals])
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
 return N,cla,gates
