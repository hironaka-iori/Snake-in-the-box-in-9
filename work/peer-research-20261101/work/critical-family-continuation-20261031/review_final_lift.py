from pathlib import Path
import sys,json,gzip,hashlib,array,collections,itertools
H=Path(__file__).resolve().parent;sys.path.insert(0,str(H))
from compact_history_lift import AC,lift
def canonical(w):
 seen=[];out=[]
 for x in w:
  if x not in seen:seen.append(x)
  out.append(seen.index(x))
 return out
base=json.loads((H/'filtered_critical_edges.json').read_text());byid={e['source_edge']:e for e in base};patterns=[tuple(p) for p in json.loads((H/'forbidden_patterns.json').read_text())];assert len(patterns)==222
proofs=[];trials=0;max_frontier=0
for k,p in enumerate(patterns):
 C=[byid[t] for t in p];assert all(a['v']==b['u'] for a,b in zip(C,C[1:]));first=C[0]['directions'];vs=[0]
 for a in first:vs.append(vs[-1]^(1<<a))
 assert all((a^b).bit_count()>1 for i,a in enumerate(vs) for j,b in enumerate(vs) if j>i+1)
 frontier=[(first,vs)]
 for e in C[1:]:
  nxt=[]
  for d,vertices in frontier:
   for a in range(9):
    trials+=1;dd=d+[a]
    if canonical(dd[-9:])!=e['directions']:continue
    x=vertices[-1]^(1<<a)
    if all((x^v).bit_count()>1 for v in vertices[:-1]):nxt.append((dd,vertices+[x]))
  frontier=nxt;max_frontier=max(max_frontier,len(nxt));assert len(nxt)<1000000
  if not frontier:break
 assert not frontier,(k,p)
 proofs.append({'pattern_index':k,'length':len(p)})
ac=AC(patterns);prefixes=ac.prefix;index={p:q for q,p in enumerate(prefixes)};patternset=set(patterns)
def suffixstep(q,t):
 w=prefixes[q]+(t,);candidates=[s for s in prefixes_by_last.get(t,[]) if len(s)<=len(w) and w[-len(s):]==s]
 return index[max(candidates,key=len)] if candidates else 0
prefixes_by_last=collections.defaultdict(list)
for p in prefixes:
 if p:prefixes_by_last[p[-1]].append(p)
assert set(prefixes)=={()}|{p[:j] for p in patterns for j in range(1,len(p)+1)}
for q,p in enumerate(prefixes):
 proper=[s for s in prefixes_by_last.get(p[-1],[]) if len(s)<len(p) and p[-len(s):]==s] if p else []
 fail=index[max(proper,key=len)] if proper else 0;assert ac.fail[q]==fail
 bad=any(len(p)>=len(z) and p[-len(z):]==z for z in patterns);assert ac.bad[q]==bad
raw=(H/'final_lift.json.gz').read_bytes();d=json.loads(gzip.decompress(raw));assert d['patterns']==[list(p) for p in patterns];states=[tuple(s) for s in d['states']];stateid={s:i for i,s in enumerate(states)};edges=d['edges'];originalnodes=sorted({v for e in base for v in [e['u'],e['v']]})
assert states[:len(originalnodes)]==[(v,0) for v in originalnodes]
assert len(states)==len(stateid)
for q,p in enumerate(prefixes):
 if q and not ac.bad[q]:assert (byid[p[-1]]['v'],q) in stateid
assert len(states)==len(originalnodes)+sum(q>0 and not ac.bad[q] for q in range(len(prefixes)))
actual={};adj=collections.defaultdict(list)
for e in base:adj[e['u']].append(e)
for j,e in enumerate(edges):
 assert e['source_edge']==j;key=(e['u'],e['projection']);assert key not in actual;actual[key]=e
expected=0
for s,(v,q) in enumerate(states):
 assert not ac.bad[q]
 if q:assert byid[prefixes[q][-1]]['v']==v
 for e in adj[v]:
  nq=suffixstep(q,e['source_edge']);key=(s,e['source_edge'])
  if ac.bad[nq]:assert key not in actual;continue
  expected+=1;z=actual[key];assert z['v']==stateid[e['v'],nq] and z['weight']==e['weight'];assert states[z['v']][0]==e['v']
assert expected==len(edges)
pi_raw=gzip.decompress((H/'frozen_potential.i64.gz').read_bytes());meta=json.loads((H/'frozen_source_analysis.json').read_text());assert hashlib.sha256(pi_raw).hexdigest()==meta['potential_sha256'];pi=array.array('q');pi.frombytes(pi_raw)
if sys.byteorder!='little':pi.byteswap()
assert all(e['weight']+pi[states[e['u']][0]]-pi[states[e['v']][0]]==480 for e in edges)
att=json.loads((H/'final_lift_verification.json').read_text())['attaining_cycle']
for j,e in enumerate(att):
 z=actual[e['lift_u'],e['source_edge']];assert z['v']==e['lift_v'] and z['weight']==e['weight'] and e['lift_v']==att[(j+1)%len(att)]['lift_u'];assert states[e['lift_u']][0]==e['original_u'] and states[e['lift_v']][0]==e['original_v']
assert len(att)==10 and sum(e['weight'] for e in att)==4800
# Exhaust all valid toy walks with overlapping patterns, suffix matches, terminal ancestors and multiple vertices.
toy=[{'source_edge':0,'u':0,'v':0,'weight':1},{'source_edge':1,'u':0,'v':0,'weight':2},{'source_edge':2,'u':0,'v':1,'weight':3},{'source_edge':3,'u':1,'v':0,'weight':4},{'source_edge':4,'u':1,'v':1,'weight':5}];tp=[(0,1,0),(1,0),(0,0,1),(2,3,0),(0,2,3),(3,2),(1,0,2,4)];ts,te,ta=lift(toy,tp);tout=collections.defaultdict(list);orig=collections.defaultdict(list)
for e in te:tout[e['u']].append(e)
for e in toy:orig[e['u']].append(e)
toychecks=0
def walk(v,s,h,depth):
 global toychecks
 bad=any(tuple(h[i:i+len(p)])==p for p in tp for i in range(max(0,len(h)-len(p)+1)));assert bad==(s is None);toychecks+=1
 if depth:
  for e in orig[v]:
   matches=[] if s is None else [x for x in tout[s] if x['projection']==e['source_edge']];assert len(matches)<=1
   walk(e['v'],matches[0]['v'] if matches else None,h+[e['source_edge']],depth-1)
for v in [0,1]:walk(v,ts.index((v,0)),[],9)
# Separate iterative two-pass SCC check; no use of the producer's SCC routine.
N=len(states);out_adj=[[] for _ in states];rev_adj=[[] for _ in states]
for e in edges:out_adj[e['u']].append(e['v']);rev_adj[e['v']].append(e['u'])
seen=set();order=[]
for root in range(N):
 if root in seen:continue
 stack=[(root,False)]
 while stack:
  v,done=stack.pop()
  if done:order.append(v);continue
  if v in seen:continue
  seen.add(v);stack.append((v,True));stack.extend((w,False) for w in out_adj[v] if w not in seen)
labels={};groups=[]
for root in reversed(order):
 if root in labels:continue
 k=len(groups);members=[];stack=[root];labels[root]=k
 while stack:
  v=stack.pop();members.append(v)
  for w in rev_adj[v]:
   if w not in labels:labels[w]=k;stack.append(w)
 groups.append(members)
internal=collections.Counter(labels[e['u']] for e in edges if labels[e['u']]==labels[e['v']]);cyclic=sorted((len(g),internal[k]) for k,g in enumerate(groups) if len(g)>1 or any(w==g[0] for w in out_adj[g[0]]))
assert cyclic==sorted([(3166,9991),(3839,12306),(426,708)])
reachable=set(range(len(originalnodes)));todo=list(reachable)
while todo:
 for w in out_adj[todo.pop()]:
  if w not in reachable:reachable.add(w);todo.append(w)
assert all(e['lift_u'] in reachable for e in att)
assert all(e['weight']+pi[e['u']]-pi[e['v']]==480 for e in base)
out={'status':'PASS','all_explicit_patterns':len(patterns),'independent_all9_coordinate_trials':trials,'largest_uncompressed_geometry_frontier':max_frontier,'geometry_dedup_or_fresh_symmetry_used':False,'AC_prefix_states':len(prefixes),'lift_states':len(states),'lift_edges_checked_exactly':len(edges),'all_pulled_back_slacks':0,'independent_cyclic_SCC_sizes_edges':cyclic,'reachable_states_from_all_base_zero_states':len(reachable),'attaining_cycle_reachable_from_base':True,'tight_mean':480,'attaining_cycle_edges':len(att),'attaining_cycle_weight':4800,'overlapping_pattern_toy_walk_checks':toychecks,'final_lift_bytes_sha256':hashlib.sha256(raw).hexdigest(),'source_hashes':{n:hashlib.sha256((H/n).read_bytes()).hexdigest() for n in ['forbidden_patterns.json','compact_history_lift.py','filtered_critical_edges.json']},'scope':'explicit filtered frozen lifted subgraph only; complete current model not recomputed','new_global_bound':None}
(H/'final_independent_review.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
