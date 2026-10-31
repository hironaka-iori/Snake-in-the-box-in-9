from itertools import combinations
from pathlib import Path
import json,time

def comps(adj,allowed):
 unseen=set(allowed);out=[]
 while unseen:
  v=min(unseen);todo=[v];unseen.remove(v);c={v}
  while todo:
   for w in adj[todo.pop()]&unseen:unseen.remove(w);c.add(w);todo.append(w)
  out.append(c)
 return out

def chains(adj,h):
 reachable=next(c for c in comps(adj,adj) if h in c)
 disc={};low={};stack=[];blocks=[];timer=0
 def dfs(v,parent=None):
  nonlocal timer
  timer+=1;disc[v]=low[v]=timer
  for w in sorted(adj[v]):
   if w not in disc:
    stack.append((v,w));dfs(w,v);low[v]=min(low[v],low[w])
    if low[w]>=disc[v]:
     b=set()
     while True:
      e=stack.pop();b.update(e)
      if e==(v,w):break
     blocks.append(b)
   elif w!=parent and disc[w]<disc[v]:stack.append((v,w));low[v]=min(low[v],disc[w])
 dfs(h)
 if not blocks:return [{h}]
 arts={v for v in reachable if sum(v in b for b in blocks)>1}
 tree={('b',i):set() for i in range(len(blocks))}
 for a in arts:
  tree['a',a]=set()
  for i,b in enumerate(blocks):
   if a in b:tree['a',a].add(('b',i));tree['b',i].add(('a',a))
 root=('a',h) if h in arts else ('b',next(i for i,b in enumerate(blocks) if h in b))
 out=[]
 def walk(v,parent,U):
  U=U|(blocks[v[1]] if v[0]=='b' else {v[1]})
  children=tree[v]-{parent}
  if not children:out.append(U)
  for w in children:walk(w,v,U)
 walk(root,None,set());return out

def pathsets(adj,h):
 out=[]
 def dfs(v,seen):
  out.append(frozenset(seen))
  for w in adj[v]-seen:dfs(w,seen|{w})
 dfs(h,{h});return out

def color(adj,h):
 c={h:0};todo=[h]
 while todo:
  v=todo.pop()
  for w in adj[v]:
   if w in c and c[w]==c[v]:return None
   if w not in c:c[w]=1-c[v];todo.append(w)
 return c

def main():
 start=time.perf_counter();graphs=roots=paths=sepchecks=biproots=0
 pairs=list(combinations(range(5),2))
 for mask in range(1<<len(pairs)):
  adj={v:set() for v in range(5)}
  for i,(u,v) in enumerate(pairs):
   if mask>>i&1:adj[u].add(v);adj[v].add(u)
  graphs+=1
  for h in adj:
   roots+=1;sets=pathsets(adj,h);paths+=len(sets);us=chains(adj,h)
   assert all(any(p<=u for u in us) for p in sets)
   longest=max(map(len,sets));c=color(adj,h)
   if c is not None:
    biproots+=1;bound=max(min(2*sum(c[v]==0 for v in u),2*sum(c[v]==1 for v in u)+1) for u in us);assert longest<=bound
   for k in [0,1,2]:
    for Kt in combinations(adj,k):
     K=set(Kt);cc=comps(adj,set(adj)-K)
     if h in K:bound=k+sum(sorted(map(len,cc),reverse=True)[:k+1])
     else:
      hc=next(c for c in cc if h in c);bound=k+len(hc)+sum(sorted([len(c) for c in cc if c is not hc],reverse=True)[:k])
     assert longest<=bound;sepchecks+=1
 V={0,1,3,7,6,4,11,14};adj={v:{w for w in V if (v^w).bit_count()==1} for v in V};P=[0,1,3,7,6,14]
 assert all(((a^b).bit_count()==1)==(j==i+1) for i,a in enumerate(P) for j,b in enumerate(P) if j>i)
 us=chains(adj,0);c=color(adj,0);good=max(min(2*sum(c[v]==0 for v in u),2*sum(c[v]==1 for v in u)+1) for u in us)
 badus=[set(V)-{3,11},set(V)-{6,14}];bad=max(min(2*sum(c[v]==0 for v in u),2*sum(c[v]==1 for v in u)+1) for u in badus)
 assert good==6 and bad==4
 # Independent induced counterexample to per-component single-path capacities.
 A={i:set() for i in range(11)}
 def edge(u,v):A[u].add(v);A[v].add(u)
 for i in range(1,5):edge(0,i);edge(i,i+4)
 for u,v in [(6,9),(9,7),(7,10),(10,8)]:edge(u,v)
 witness=[5,1,0,2,6,9,7,10,8]
 assert all((b in A[a])==(j==i+1) for i,a in enumerate(witness) for j,b in enumerate(witness) if j>i)
 component={i:A[i]&set(range(9)) for i in range(9)}
 assert max(len(z) for v in component for z in pathsets(component,v))==5
 out={'all_five_vertex_graphs':graphs,'root_cases':roots,'enumerated_simple_paths':paths,'separator_bound_checks':sepchecks,'bipartite_root_cases':biproots,'block_chain_containment':'PASS','separator_rules':'PASS','off_chain_cutvertex_counterexample':{'V':sorted(V),'path':P,'correct_bound':good,'incorrect_omission_bound':bad},'single_path_component_capacity_counterexample':{'induced_global_path':witness,'true_size':9,'incorrect_bound':7},'seconds':time.perf_counter()-start}
 Path(__file__).with_name('independent_checks.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
if __name__=='__main__':main()
