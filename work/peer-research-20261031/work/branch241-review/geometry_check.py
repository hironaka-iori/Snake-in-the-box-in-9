"""Independent geometric/model checks, separate from the CDCL solver."""
def verify_cycle(vertices,n=9):
 C=set(vertices)
 if len(C)!=len(vertices) or len(C)<4 or any(not 0<=x<1<<n for x in C):raise ValueError('invalid cycle vertices')
 adj={x:[x^(1<<d) for d in range(n) if x^(1<<d) in C] for x in C}
 if any(len(ns)!=2 for ns in adj.values()):raise ValueError('cut is not an induced 2-regular cube subgraph')
 seen=set();todo=[min(C)]
 while todo:
  v=todo.pop()
  if v in seen:continue
  seen.add(v);todo.extend(adj[v])
 if seen!=C:raise ValueError('cut cycle is disconnected')
 return {'vertices':len(C),'induced_connected_2regular':True}
def components(selected,n=9):
 S=set(selected);seen=set();out=[]
 for root in sorted(S):
  if root in seen:continue
  todo=[root];comp=[];seen.add(root)
  while todo:
   v=todo.pop();comp.append(v)
   for d in range(n):
    w=v^(1<<d)
    if w in S and w not in seen:seen.add(w);todo.append(w)
  out.append(sorted(comp))
 return out
def verify_global_snake(selected,window,n=9):
 S=set(selected)
 if len(S)!=len(selected) or not set(window)<=S:raise ValueError('missing fixed window or repeated vertices')
 deg={v:sum(v^(1<<d) in S for d in range(n)) for v in S}
 if any(d not in (1,2) for d in deg.values()) or sum(d==1 for d in deg.values())!=2 or len(components(S,n))!=1:raise ValueError('not one induced path')
 ends=[x for x in S if deg[x]==1];path=[];prev=None;v=min(ends)
 while True:
  path.append(v);nxt=[v^(1<<d) for d in range(n) if v^(1<<d) in S and v^(1<<d)!=prev]
  if not nxt:break
  prev,v=v,nxt[0]
 if len(path)!=len(S):raise ValueError('path traversal mismatch')
 # Full pairwise inducedness, independently of the degree-based traversal.
 for i,a in enumerate(path):
  for j in range(i+1,len(path)):
   if ((a^path[j]).bit_count()==1)!=(j==i+1):raise ValueError('pairwise inducedness failure')
 return {'edges':len(path)-1,'vertices':path,'all_pairs_checked':len(path)*(len(path)-1)//2}
