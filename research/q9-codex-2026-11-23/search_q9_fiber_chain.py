from collections import Counter
nb=[[v^(1<<d) for d in range(5)] for v in range(32)]
mask=[sum(1<<u for u in ns) for ns in nb]
def walks(path,seen,ban):
 if len(path)>=9: yield (tuple(path),seen)
 for u in nb[path[-1]]:
  if (1<<u)&ban:continue
  yield from walks(path+[u],seen|(1<<u),ban|mask[path[-1]]|(1<<u))
base=list(walks([0],1,1))
def shift(bits,t):return sum(1<<(u^t) for u in range(32) if bits>>u&1)
opts=[(p,m) for p,m in base if len(p)==14]
def findpair():
 for p,m in opts:
  for q,n in opts:
   for t in range(32):
    if m&shift(n,t)==0:return (p,m),(tuple(u^t for u in q),shift(n,t))
a,b=findpair()
assert a[1]&b[1]==0 and len(a[0])==len(b[0])==14
def families(seeds,r):
 banks=[set(),set()]
 for p,m in base:
  for t in range(32):
   s=shift(m,t)
   for i,(_,template) in enumerate(seeds):
    if (template&~s).bit_count()<=r:
     banks[i].add((p[0]^t,p[-1]^t,s))
 return banks

def chain(banks,target,any_order=False,cell_count=16):
 banks=[sorted(g) for g in banks]
 successors=[]
 for side,bank in enumerate(banks):
  other=banks[1-side]
  by_start=[0]*32
  occupied=[0]*32
  for j,(v,end,m) in enumerate(other):
   by_start[v]|=1<<j
   inside=m
   while inside:
    bit=inside & -inside;inside-=bit
    occupied[bit.bit_length()-1]|=1<<j
  links=[]
  for start,end,m in bank:
   options=by_start[end]
   forbidden=m^(1<<end)
   while options and forbidden:
    bit=forbidden & -forbidden;forbidden-=bit
    options &= ~occupied[bit.bit_length()-1]
   row=[]
   while options:
    bit=options & -options;options-=bit;row.append(bit.bit_length()-1)
   links.append(row)
  successors.append(links)
 # Best possible score while enforcing only consecutive-fibre constraints.
 bound=[[m.bit_count() for _,_,m in banks[1]]]
 for i in reversed(range(cell_count-1)):
  side=i%2
  bound.append([m.bit_count()+max((bound[-1][j] for j in successors[side][k]),default=-1000)
                for k,(_,_,m) in enumerate(banks[side])])
 bound.reverse()
 print("states",list(map(len,banks)),"links",[sum(map(len,s)) for s in successors],
       "chain_relaxation_edge_upper",(max(bound[0])-1 if max(bound[0])>0 else None),flush=True)
 gray=[x^(x>>1) for x in range(cell_count)]
 def dfs(chosen,cells,i,k,total):
  if total+bound[i][k]<target+1:return
  start,end,m=banks[i%2][k]
  if any((cells[i]^cells[j]).bit_count()==1 and m&g for j,(_,_,g) in enumerate(chosen[:-1])):return
  chosen=chosen+[(start,end,m)]
  if i+1==cell_count:
   path=[]
   for cell,(v,end,occupied) in zip(cells,chosen):
    left=occupied
    while True:
     path.append((cell<<5)|v);left ^= 1<<v
     if not left:break
     options=[u for u in nb[v] if left>>u&1]
     assert len(options)==1
     v=options[0]
    assert v==end
   assert len(path)>=target+1 and len(path)==len(set(path))
   assert all(((u^path[j]).bit_count()==1)==(j==h+1) for h,u in enumerate(path) for j in range(h+1,len(path)))
   return path
  if any_order:
   used_axes=0
   for u,v in zip(cells,cells[1:]):used_axes |= u^v
   max_axis=min(4,used_axes.bit_length()+1)
   next_cells=[cells[-1]^(1<<d) for d in range(max_axis)]
  else:
   next_cells=[gray[i+1]]
  for cell in next_cells:
   if cell in cells:continue
   for j in successors[i%2][k]:
    result=dfs(chosen,cells+[cell],i+1,j,total+m.bit_count())
    if result:return result
 for k in sorted(range(len(banks[0])),key=lambda k:-bound[0][k]):
  result=dfs([],[0],0,k,0)
  if result:return result
 return None
if __name__=="__main__":
 import argparse
 ap=argparse.ArgumentParser()
 ap.add_argument("--radius",type=int,default=3)
 ap.add_argument("--target",type=int,default=192)
 ap.add_argument("--any-order",action="store_true")
 ap.add_argument("--cells",type=int,choices=(2,4,8,16),default=16)
 args=ap.parse_args()
 bank=families([a,b],args.radius)
 print("result",chain(bank,args.target,args.any_order,args.cells),flush=True)
