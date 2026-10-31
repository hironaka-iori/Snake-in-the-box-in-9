from pathlib import Path
import json,gzip,hashlib,array,sys,collections
H=Path(__file__).resolve().parent;sys.path.insert(0,str(H))
from compact_history_lift import AC
base=json.loads((H/'filtered_critical_edges.json').read_text());B={e['source_edge']:e for e in base};patterns=[tuple(tuple(w) for w in p) for p in json.loads((H/'short_closure_patterns.json').read_text())];assert len(patterns)==431 and len(set(patterns))==431
# Independent all-nine-coordinate geometry; no representative fresh choices or state dedup.
def canon(w):
 seen=[];out=[]
 for x in w:
  if x not in seen:seen.append(x)
  out.append(seen.index(x))
 return tuple(out)
geometry_trials=0;largest_geometry_frontier=0
for pattern in patterns:
 first=list(pattern[0]);vs=[0]
 for a in first:vs.append(vs[-1]^(1<<a))
 assert canon(first)==tuple(first) and all((a^b).bit_count()>1 for i,a in enumerate(vs) for j,b in enumerate(vs) if j>i+1)
 frontier=[(first,vs)]
 for word in pattern[1:]:
  nxt=[]
  for directions,vertices in frontier:
   for coord in range(9):
    geometry_trials+=1;d=directions+[coord]
    if canon(d[-9:])!=word:continue
    x=vertices[-1]^(1<<coord)
    if all((x^v).bit_count()>1 for v in vertices[:-1]):nxt.append((d,vertices+[x]))
  frontier=nxt;largest_geometry_frontier=max(largest_geometry_frontier,len(nxt));assert len(nxt)<1000000
  if not frontier:break
 assert not frontier
ac=AC(patterns);prefixes=ac.prefix;prefixid={p:q for q,p in enumerate(prefixes)};bylast=collections.defaultdict(list)
for p in prefixes:
 if p:bylast[p[-1]].append(p)
assert set(prefixes)=={()}|{p[:j] for p in patterns for j in range(1,len(p)+1)}
for q,p in enumerate(prefixes):
 cand=[z for z in bylast.get(p[-1],[]) if len(z)<len(p) and p[-len(z):]==z] if p else []
 expected=prefixid[max(cand,key=len)] if cand else 0;assert ac.fail[q]==expected
 assert ac.bad[q]==any(len(p)>=len(z) and p[-len(z):]==z for z in patterns)
cache={}
def delta(q,w):
 key=(q,w)
 if key not in cache:
  text=prefixes[q]+(w,);cand=[p for p in bylast.get(w,[]) if len(p)<=len(text) and text[-len(p):]==p];cache[key]=prefixid[max(cand,key=len)] if cand else 0
 return cache[key]
raw=(H/'short_closure_lift.json.gz').read_bytes();D=json.loads(gzip.decompress(raw));states=[tuple(s) for s in D['states']];edges=D['edges'];ids={s:i for i,s in enumerate(states)};assert len(ids)==len(states)
nodes=sorted({v for e in base for v in [e['u'],e['v']]});assert states[:len(nodes)]==[(v,0) for v in nodes]
adj=collections.defaultdict(list)
for e in base:adj[e['u']].append(e)
actual={}
for j,e in enumerate(edges):
 assert e['source_edge']==j and (e['u'],e['projection']) not in actual;actual[e['u'],e['projection']]=e
expected=0;forbidden=0
for s,(v,q) in enumerate(states):
 assert v in adj or v in nodes;assert 0<=q<len(prefixes) and not ac.bad[q]
 for e in adj[v]:
  nq=delta(q,tuple(e['directions']));key=(s,e['source_edge'])
  if ac.bad[nq]:assert key not in actual;forbidden+=1;continue
  z=actual[key];assert z['v']==ids[e['v'],nq] and z['weight']==e['weight'];expected+=1
assert expected==len(edges)
N=len(states);out=[[] for _ in states];rev=[[] for _ in states]
for e in edges:out[e['u']].append(e['v']);rev[e['v']].append(e['u'])
reachable=set(range(len(nodes)));todo=list(reachable)
while todo:
 for w in out[todo.pop()]:
  if w not in reachable:reachable.add(w);todo.append(w)
assert len(reachable)==N
seen=set();order=[]
for root in range(N):
 if root in seen:continue
 stack=[(root,False)]
 while stack:
  v,done=stack.pop()
  if done:order.append(v);continue
  if v in seen:continue
  seen.add(v);stack.append((v,True));stack.extend((w,False) for w in out[v] if w not in seen)
labels={};groups=[]
for root in reversed(order):
 if root in labels:continue
 k=len(groups);g=[];todo=[root];labels[root]=k
 while todo:
  v=todo.pop();g.append(v)
  for w in rev[v]:
   if w not in labels:labels[w]=k;todo.append(w)
 groups.append(g)
internal=collections.Counter(labels[e['u']] for e in edges if labels[e['u']]==labels[e['v']]);cyc=[(k,g) for k,g in enumerate(groups) if len(g)>1 or g[0] in out[g[0]]];sizes=sorted((len(g),internal[k]) for k,g in cyc);assert sizes==sorted([(35345,119647),(47650,162742)])
nodecomp={}
for e in base:
 for v in [e['u'],e['v']]:assert v not in nodecomp or nodecomp[v]==e['component'];nodecomp[v]=e['component']
oldcycliccomponents=sorted({nodecomp[states[s][0]] for _,g in cyc for s in g});assert 264110 not in oldcycliccomponents
pi_raw=gzip.decompress((H/'frozen_potential.i64.gz').read_bytes());meta=json.loads((H/'frozen_source_analysis.json').read_text());assert hashlib.sha256(pi_raw).hexdigest()==meta['potential_sha256'];pi=array.array('q');pi.frombytes(pi_raw)
if sys.byteorder!='little':pi.byteswap()
assert all(e['weight']+pi[states[e['u']][0]]-pi[states[e['v']][0]]==480 for e in edges)
att=json.loads((H/'short_closure_lift_verification.json').read_text())['attaining_cycle']
for j,e in enumerate(att):
 z=actual[e['lift_u'],e['source_edge']];assert z['v']==e['lift_v'] and z['weight']==e['weight'] and e['lift_v']==att[(j+1)%len(att)]['lift_u']
assert att and sum(e['weight'] for e in att)==480*len(att)
result={'status':'PASS','all_patterns_independently_geometrically_refuted':True,'all_nine_coordinate_geometry_trials':geometry_trials,'largest_geometry_frontier':largest_geometry_frontier,'direction_patterns':431,'AC_prefix_states':len(prefixes),'lift_states':N,'lift_edges_checked':len(edges),'forbidden_outgoing_transitions_checked':forbidden,'independent_suffix_transition_pairs':len(cache),'all_states_reachable_from_base_empty_history':True,'cyclic_SCC_vertices_edges':sizes,'old_components_with_cyclic_lifts':oldcycliccomponents,'old_component264110_cyclic_structure_absent':True,'all_edges_exactly_tight':480,'attaining_cycle_length':len(att),'attaining_cycle_weight':sum(e['weight'] for e in att),'exact_minimum_cycle_mean_of_this_explicit_subgraph':480,'full_current_graph_recomputed':False,'new_global_bound':None,'source_hashes':{n:hashlib.sha256((H/n).read_bytes()).hexdigest() for n in ['direction_history_lift.py','evaluate_short_closure.py','short_direction_closure.py','short_closure_patterns.json','short_closure_lift.json.gz','filtered_critical_edges.json']}}
(H/'review_short_closure.json').write_text(json.dumps(result,indent=2));print(json.dumps(result,indent=2))
