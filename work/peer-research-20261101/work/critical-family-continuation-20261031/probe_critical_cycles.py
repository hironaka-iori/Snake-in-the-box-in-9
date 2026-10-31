"""Find short tight cycles and test their literal-coordinate realizability.
Fresh-coordinate symmetry is exact: permutations fix every previously used coordinate.
All historically used coordinates absent from the overlap remain separate choices.
"""
from pathlib import Path
from collections import defaultdict,deque,Counter
import json,time,hashlib
H=Path(__file__).resolve().parent

def canon(word):
 seen={};return [seen.setdefault(v,len(seen)) for v in word]

def scc(edges):
 adj=defaultdict(list);rev=defaultdict(list)
 for e in edges:adj[e['u']].append(e['v']);rev[e['v']].append(e['u']);adj[e['v']];rev[e['u']]
 seen=set();order=[]
 for root in adj:
  if root in seen:continue
  seen.add(root);stack=[(root,iter(adj[root]))]
  while stack:
   v,it=stack[-1];w=next(it,None)
   if w is None:order.append(v);stack.pop()
   elif w not in seen:seen.add(w);stack.append((w,iter(adj[w])))
 comps=[];labels={}
 for root in reversed(order):
  if root in labels:continue
  k=len(comps);S={root};labels[root]=k;todo=[root]
  while todo:
   v=todo.pop()
   for w in rev[v]:
    if w not in labels:labels[w]=k;S.add(w);todo.append(w)
  comps.append(S)
 return comps,labels

def shortest_cycle(adj,root,maxdepth=16):
 q=deque([root]);parents={root:None};depth={root:0}
 while q:
  v=q.popleft()
  if depth[v]>=maxdepth:continue
  for e in adj.get(v,[]):
   w=e['v']
   if w==root:
    result=[e];x=v
    while parents[x] is not None:
     prev,edge=parents[x];result.append(edge);x=prev
    return result[::-1]
   if w not in parents:parents[w]=(v,e);depth[w]=depth[v]+1;q.append(w)
 return None

def realize(C,max_edges=48,max_states=10000):
 d=canon(C[0]['directions']);vertices=[0]
 for a in d:vertices.append(vertices[-1]^(1<<a))
 if len(set(vertices))<len(vertices) or any((a^b).bit_count()==1 for i,a in enumerate(vertices) for j,b in enumerate(vertices) if j>i+1):return {'status':'REFUTED','forbidden_edges':1,'levels':[]}
 frontier=[(d,vertices)];levels=[];states=1
 for count in range(2,max_edges+1):
  abstract=C[(count-1)%len(C)]['directions'];nxt={};reasons=Counter();trials=0
  for d,vertices in frontier:
   mapping={};good=True
   for a,b in zip(abstract[:8],d[-8:]):
    if a in mapping and mapping[a]!=b:good=False;break
    mapping[a]=b
   if not good or len(set(mapping.values()))!=len(mapping):reasons['incompatible_overlap']+=1;continue
   if abstract[-1] in mapping:choices=[mapping[abstract[-1]]]
   else:
    used=set(d);choices=[k for k in sorted(used) if k not in mapping.values()]
    fresh=[k for k in range(9) if k not in used]
    if fresh:choices.append(fresh[0])
   for a in choices:
    trials+=1;x=vertices[-1]^(1<<a)
    if any((x^v).bit_count()<=1 for v in vertices[:-1]):reasons['repeat_or_chord']+=1;continue
    nd=d+[a];nv=vertices+[x];key=(tuple(nd[-8:]),x,sum(1<<v for v in nv),sum(1<<z for z in set(nd)));nxt[key]=(nd,nv)
  frontier=list(nxt.values());states+=len(frontier);levels.append({'model_edges':count,'literal_transitions':8+count,'live_canonical_states':len(frontier),'candidate_trials':trials,'rejections':dict(reasons)})
  if not frontier:return {'status':'REFUTED','forbidden_edges':count,'canonical_states':states,'levels':levels}
  if states>=max_states:return {'status':'STATE_LIMIT','canonical_states':states,'levels':levels,'witness_directions':frontier[0][0]}
 return {'status':'DEPTH_LIMIT','canonical_states':states,'levels':levels,'witness_directions':frontier[0][0]}

def run():
 start=time.perf_counter();edges=json.loads((H/'filtered_critical_edges.json').read_text());comps,labels=scc(edges);inside=defaultdict(list)
 for e in edges:
  if labels[e['u']]==labels[e['v']]:inside[labels[e['u']]].append(e)
 rows=[];summaries=[];dedup=set()
 for k,S in enumerate(comps):
  E=inside[k]
  if len(S)==1 and not any(e['u']==e['v'] for e in E):continue
  original=sorted({e['component'] for e in E});summaries.append({'component':k,'states':len(S),'edges':len(E),'frozen_component_ids':original})
  adj=defaultdict(list)
  for e in E:adj[e['u']].append(e)
  nodes=sorted(S);seeds=nodes if len(nodes)<=48 else [nodes[j*(len(nodes)-1)//47] for j in range(48)]
  for root in seeds:
   C=shortest_cycle(adj,root)
   if not C:continue
   ids=tuple(e['source_edge'] for e in C);key=min(ids[j:]+ids[:j] for j in range(len(ids)))
   if key in dedup:continue
   dedup.add(key);r=realize(C);r.update({'component':k,'frozen_components':original,'cycle_length':len(C),'source_edge_ids':list(ids),'mean':sum(e['weight'] for e in C)/len(C),'directions':[e['directions'] for e in C]});rows.append(r)
  print(json.dumps({'states':len(S),'edges':len(E),'candidate_cycles_so_far':len(rows),'statuses':dict(Counter(r['status'] for r in rows))}),flush=True)
 out={'source_scope':'filtered frozen critical subset only','SCCs':summaries,'candidate_cycles':rows,'status_counts':dict(Counter(r['status'] for r in rows)),'seconds':time.perf_counter()-start,'full_current_graph_recomputed':False,'new_global_bound':None}
 (H/'critical_cycle_probes.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items() if k not in ['candidate_cycles','SCCs']},indent=2))
if __name__=='__main__':run()
