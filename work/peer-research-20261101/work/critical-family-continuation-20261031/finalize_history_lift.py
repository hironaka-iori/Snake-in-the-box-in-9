"""Build the final compact lift and certify a surviving exact mean-480 cycle."""
from pathlib import Path
from collections import defaultdict
from fractions import Fraction
import json,gzip,array,sys,hashlib
from compact_history_lift import lift
from probe_critical_cycles import scc,shortest_cycle
H=Path(__file__).resolve().parent
base=json.loads((H/'filtered_critical_edges.json').read_text());run=json.loads((H/'history_separation.json').read_text());patterns={tuple(p) for p in run['forbidden_patterns']}
for r in run['rounds'][-1]['checked_cycles']:
 if r['status']=='REFUTED':
  ids=r['projected_ids'];patterns.add(tuple(ids[j%len(ids)] for j in range(r['forbidden_edges'])))
patterns=sorted(patterns);states,edges,ac=lift(base,patterns);comps,labels=scc(edges);inside=defaultdict(list)
for e in edges:
 if labels[e['u']]==labels[e['v']]:inside[labels[e['u']]].append(e)
cyclic=[(k,S,inside[k]) for k,S in enumerate(comps) if len(S)>1 or any(e['u']==e['v'] for e in inside[k])]
raw=gzip.decompress((H/'frozen_potential.i64.gz').read_bytes());meta=json.loads((H/'frozen_source_analysis.json').read_text());assert hashlib.sha256(raw).hexdigest()==meta['potential_sha256'];pi=array.array('q');pi.frombytes(raw)
if sys.byteorder!='little':pi.byteswap()
assert all(e['weight']+pi[states[e['u']][0]]-pi[states[e['v']][0]]==480 for e in edges)
k,S,E=min(cyclic,key=lambda x:len(x[1]));adj=defaultdict(list)
for e in E:adj[e['u']].append(e)
cycle=shortest_cycle(adj,min(S),maxdepth=10000);assert cycle
assert all(cycle[i]['v']==cycle[(i+1)%len(cycle)]['u'] for i in range(len(cycle)))
mu=Fraction(sum(e['weight'] for e in cycle),len(cycle));assert mu==480
cycle_saved=[{'lift_u':e['u'],'lift_v':e['v'],'original_u':states[e['u']][0],'original_v':states[e['v']][0],'weight':e['weight'],'source_edge':e['projection']} for e in cycle]
report={'status':'EXACT_MEAN_480_ON_EXPLICIT_LIFTED_SUBGRAPH','frozen_critical_records':18865,'filtered_records':len(base),'patterns':len(patterns),'base_vertices':len({v for e in base for v in [e['u'],e['v']]}),'lift_vertices':len(states),'extra_vertices':len(states)-len({v for e in base for v in [e['u'],e['v']]}),'lift_edges':len(edges),'AC_states':len(ac.next),'surviving_cyclic_SCCs':[{'states':len(S),'edges':len(E)} for _,S,E in cyclic],'all_edges_exactly_tight_at_mean':480,'attaining_cycle_length':len(cycle),'attaining_cycle_total_weight':sum(e['weight'] for e in cycle),'attaining_cycle':cycle_saved,'mean':str(mu),'full_current_4957613_edge_graph_loaded':False,'new_global_bound':None,'inference_scope':'A source-preserving filtered-subgraph embedding into the current model follows the shared base arrays and case rules; this does not discharge the geometric snake-to-graph bridge.'}
(H/'final_lift_verification.json').write_text(json.dumps(report,indent=2)+'\n');(H/'forbidden_patterns.json').write_text(json.dumps([list(p) for p in patterns],indent=2)+'\n')
with gzip.open(H/'final_lift.json.gz','wt',encoding='utf-8') as f:json.dump({'states':states,'edges':edges,'patterns':[list(p) for p in patterns]},f,separators=(',',':'))
print(json.dumps({k:v for k,v in report.items() if k!='attaining_cycle'},indent=2))
