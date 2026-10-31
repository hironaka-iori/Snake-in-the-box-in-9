"""Complete length-3/5 direction-history closure on the projected frozen graph.
Projection ignores count states, so it is an overapproximation; every rejected
word is independently a geometrically impossible direction history regardless.
"""
from pathlib import Path
from collections import defaultdict,Counter
import json,time
from probe_critical_cycles import realize
from advance_direction_patterns import minimize
H=Path(__file__).resolve().parent
start=time.perf_counter();base=json.loads((H/'filtered_critical_edges.json').read_text());out=defaultdict(list)
for e in base:out[e['u']].append(e)
pairs=set()
for e in base:
 for f in out[e['v']]:pairs.add((tuple(e['directions']),tuple(f['directions'])))
adj=defaultdict(set)
for a,b in pairs:adj[a].add(b);adj[b]
old=[tuple(tuple(w) for w in p) for p in json.loads((H/'direction_patterns_extended.json').read_text())];all3=[];bad3=[];bad5=[];tested=Counter();accepted=Counter();certs=[]

def test(p):
 r=realize([{'directions':list(w)} for w in p],max_edges=len(p),max_states=100000)
 tested[len(p)]+=1
 if r['status']=='REFUTED':certs.append({'directions':[list(w) for w in p],'geometry':r});return True
 assert r['status']=='DEPTH_LIMIT';accepted[len(p)]+=1;return False
for a in sorted(adj):
 for b in sorted(adj[a]):
  for c in sorted(adj[b]):
   p=(a,b,c);all3.append(p)
   if test(p):bad3.append(p)
bad3set=set(bad3)
for p in all3:
 if p in bad3set:continue
 for d in sorted(adj[p[-1]]):
  if (p[1],p[2],d) in bad3set:continue
  for e in sorted(adj[d]):
   q=p+(d,e)
   if q[-3:] in bad3set:continue
   if test(q):bad5.append(q)
minimal=minimize(old+bad3+bad5)
(H/'short_closure_patterns.json').write_text(json.dumps([[list(w) for w in p] for p in minimal],indent=2)+'\n')
r={'status':'COMPLETE_ON_PROJECTED_DIRECTION_GRAPH','direction_symbols':len(adj),'direction_pairs':len(pairs),'word_tests':dict(tested),'geometrically_feasible':dict(accepted),'invalid_triples':len(bad3),'invalid_five_histories_without_invalid_triples':len(bad5),'merged_minimal_patterns':len(minimal),'proofs':certs,'seconds':time.perf_counter()-start,'scope':'projected frozen subgraph; no full-current-graph mean or global bound'}
(H/'short_closure_report.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({k:v for k,v in r.items() if k!='proofs'},indent=2))
