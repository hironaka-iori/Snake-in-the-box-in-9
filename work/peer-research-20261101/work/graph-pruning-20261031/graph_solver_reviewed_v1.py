"""Exact induced-path search with proved residual-graph bounds. Standard library only.
No run marked UNKNOWN is an exclusion; no claim of a new global Q9 bound.
"""
from dataclasses import dataclass,asdict
from itertools import combinations
from pathlib import Path
import argparse,json,time

def bits(mask):
 while mask:
  b=mask&-mask;yield b.bit_length()-1;mask^=b

def cube(n):return [sum(1<<(v^(1<<d)) for d in range(n)) for v in range(1<<n)]
def component(adj,allowed,h):
 seen=1<<h;todo=seen
 while todo:
  b=todo&-todo;todo^=b;v=b.bit_length()-1
  new=adj[v]&allowed&~seen;seen|=new;todo|=new
 return seen

def parity_capacity(mask,h):
 s=sum((v.bit_count()^h.bit_count())&1==0 for v in bits(mask));o=mask.bit_count()-s
 return min(2*s,2*o+1)

def blocks(adj,R,h):
 """Tarjan edge-stack blocks, including bridges and an isolated root."""
 disc={};low={};stack=[];out=[];clock=0
 def dfs(v,parent):
  nonlocal clock
  clock+=1;disc[v]=low[v]=clock
  for w in bits(adj[v]&R):
   if w==parent:continue
   if w not in disc:
    stack.append((v,w));dfs(w,v);low[v]=min(low[v],low[w])
    if low[w]>=disc[v]:
     B=0
     while True:
      a,b=stack.pop();B|=(1<<a)|(1<<b)
      if (a,b)==(v,w):break
     out.append(B)
   elif disc[w]<disc[v]:stack.append((v,w));low[v]=min(low[v],disc[w])
 dfs(h,-1)
 return out or [1<<h]

def block_bound(adj,R,h,with_parity=True,cycle_cap=True,details=False):
 """Union whole blocks along each rooted chain: off-chain cut vertices stay counted."""
 B=blocks(adj,R,h);membership={v:[] for v in bits(R)}
 for i,b in enumerate(B):
  for v in bits(b):membership[v].append(i)
 arts={v for v,bs in membership.items() if len(bs)>1}
 tree={('b',i):[] for i in range(len(B))}
 for v in arts:
  tree['a',v]=[]
  for i in membership[v]:tree['a',v].append(('b',i));tree['b',i].append(('a',v))
 root=('a',h) if h in arts else ('b',membership[h][0])
 cycles=[b.bit_count()>=4 and all((adj[v]&b).bit_count()==2 for v in bits(b)) for b in B]
 best=1;chains=[]
 def visit(node,parent,union,penalty,chain):
  nonlocal best
  if node[0]=='b':
   i=node[1];union|=B[i];penalty+=bool(cycle_cap and cycles[i]);chain=chain+[i]
  children=[w for w in tree[node] if w!=parent]
  if not children:
   bound=union.bit_count()-penalty
   if with_parity:bound=min(bound,parity_capacity(union,h))
   best=max(best,bound)
   if details:chains.append({'blocks':chain,'vertices':list(bits(union)),'cycle_blocks':penalty,'bound':bound})
  for w in children:visit(w,node,union,penalty,chain)
 visit(root,None,1<<h,0,[])
 return (best,{'blocks':[list(bits(b)) for b in B],'articulations':sorted(arts),'chains':chains}) if details else best

def separator_bound(adj,R,h,K):
 """A path visits <=k+1 components of G-K; root location sharpens the count."""
 K=set(K)
 if not K<=set(bits(R)):raise ValueError('separator outside residual graph')
 KM=sum(1<<v for v in K);remaining=R&~KM;cs=[]
 while remaining:
  b=remaining&-remaining;C=component(adj,remaining,b.bit_length()-1);remaining&=~C;cs.append(C)
 k=len(K)
 if h in K:return k+sum(sorted((c.bit_count() for c in cs),reverse=True)[:k])
 root=next(c for c in cs if c>>h&1)
 return k+root.bit_count()+sum(sorted((c.bit_count() for c in cs if c!=root),reverse=True)[:k])

def best_separator_bound(adj,R,h,pair_limit=20):
 # Restrict candidates for cost only: every tested subset gives a safe upper bound.
 vs=sorted(bits(R),key=lambda v:((adj[v]&R).bit_count(),v))[:pair_limit]
 bound=R.bit_count()
 for K in combinations(vs,2):bound=min(bound,separator_bound(adj,R,h,K))
 return bound

def leaf_bound(adj,R,h):
 """Repository-style simultaneous leaf peeling; root retained, one per round."""
 mask=R;rounds=0
 while True:
  leaves=sum(1<<v for v in bits(mask) if v!=h and (adj[v]&mask).bit_count()<=1)
  if not leaves:return mask.bit_count()+rounds
  mask&=~leaves;rounds+=1

def validate_path(adj,path):
 if len(set(path))!=len(path):raise ValueError('repeated vertex')
 for i,v in enumerate(path):
  if not 0<=v<len(adj):raise ValueError('vertex outside graph')
  for j in range(i):
   if bool(adj[v]>>path[j]&1)!=(i-j==1):raise ValueError('non-induced prefix')
 return True

@dataclass
class Stats:
 nodes:int=0;pruned_reach:int=0;pruned_parity:int=0;pruned_leaf:int=0;pruned_block:int=0;pruned_separator:int=0;memo_hits:int=0;block_checks:int=0;separator_checks:int=0

class Search:
 def __init__(self,n,target_edges,prefix=None,mode='block',node_limit=100000,seconds=30,domain=None,memo=True):
  self.n=n;self.adj=cube(n);self.target=target_edges+1;self.prefix=prefix or [0]
  validate_path(self.adj,self.prefix)
  self.domain=((1<<(1<<n))-1) if domain is None else domain
  if any(not (self.domain>>v&1) for v in self.prefix):raise ValueError('prefix outside domain')
  self.mode=mode;self.node_limit=node_limit;self.seconds=seconds;self.memo=memo;self.failed=set();self.stats=Stats();self.witness=None;self.first_block_prune=None
 def run(self):
  self.start=time.monotonic();path=self.prefix[:];visited=sum(1<<v for v in path);forbidden=0
  for v in path[:-1]:forbidden|=self.adj[v]|(1<<v)
  def dfs(h,used,banned):
   if len(path)>=self.target:self.witness=path[:];return True
   if self.stats.nodes>=self.node_limit or time.monotonic()-self.start>=self.seconds:return None
   self.stats.nodes+=1;key=(h,used)
   if self.memo and key in self.failed:self.stats.memo_hits+=1;return False
   allowed=(self.domain&~(banned|used))|(1<<h);R=component(self.adj,allowed,h);needed=self.target-len(path)+1
   def reject(kind):
    setattr(self.stats,'pruned_'+kind,getattr(self.stats,'pruned_'+kind)+1)
    if self.memo:self.failed.add(key)
    return False
   if R.bit_count()<needed:return reject('reach')
   if self.mode!='reach' and parity_capacity(R,h)<needed:return reject('parity')
   if self.mode in ['leaf','block','separator'] and leaf_bound(self.adj,R,h)<needed:return reject('leaf')
   if self.mode in ['block','separator']:
    self.stats.block_checks+=1
    if block_bound(self.adj,R,h)<needed:
     if self.first_block_prune is None:
      bb,bd=block_bound(self.adj,R,h,details=True);self.first_block_prune={'path':path[:],'residual':list(bits(R)),'needed':needed,'bounds':{'reach':R.bit_count(),'parity':parity_capacity(R,h),'leaf':leaf_bound(self.adj,R,h),'block':bb},'decomposition':bd}
     return reject('block')
   if self.mode=='separator' and R.bit_count()<=100:
    self.stats.separator_checks+=1
    if best_separator_bound(self.adj,R,h)<needed:return reject('separator')
   candidates=list(bits(self.adj[h]&allowed&~used));candidates.sort(key=lambda v:((self.adj[v]&R).bit_count(),v))
   for v in candidates:
    path.append(v);answer=dfs(v,used|(1<<v),banned|self.adj[h]|(1<<h));path.pop()
    if answer is not False:return answer
   if self.memo:self.failed.add(key)
   return False
  answer=dfs(path[-1],visited,forbidden)
  if answer:validate_path(self.adj,self.witness)
  return {'status':'SAT' if answer else ('UNSAT_EXHAUSTIVE_PYTHON' if answer is False else 'UNKNOWN'),'scope':'fixed prefix and domain only; executable search, not Lean proof','n':self.n,'target_edges':self.target-1,'prefix_vertices':len(self.prefix),'mode':self.mode,'seconds':time.monotonic()-self.start,'stats':asdict(self.stats),'failed_states':len(self.failed),'witness':self.witness,'first_block_prune':self.first_block_prune}

if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('--n',type=int,default=9);ap.add_argument('--edges',type=int,default=235);ap.add_argument('--mode',choices=['reach','parity','leaf','block','separator'],default='block');ap.add_argument('--nodes',type=int,default=20000);ap.add_argument('--seconds',type=float,default=20);ap.add_argument('--bank-entry',type=int);ap.add_argument('--keep',type=int,default=96);ap.add_argument('--output',type=Path);a=ap.parse_args()
 prefix=None
 if a.bank_entry is not None:
  bank=Path(__file__).resolve().parent.parent/'branch241-audit/repo/work/bank9.json';rows=json.loads(bank.read_text());entry=a.bank_entry
  prefix=rows[entry//2]['vertex_sequence'][::(-1 if entry%2 else 1)][:a.keep]
 s=Search(a.n,a.edges,prefix,a.mode,a.nodes,a.seconds);result=s.run();text=json.dumps(result,indent=2);print(text)
 if a.output:a.output.write_text(text+'\n')
