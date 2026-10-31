from pathlib import Path
from collections import defaultdict
import json,gzip,array,sys,time,hashlib
from direction_history_lift import lift_direction
from probe_critical_cycles import scc,shortest_cycle
H=Path(__file__).resolve().parent;base=json.loads((H/'filtered_critical_edges.json').read_text());patterns=[tuple(tuple(w) for w in p) for p in json.loads((H/'short_closure_patterns.json').read_text())]
result,report=lift_direction(base,patterns,state_limit=250000,seconds=30)
if result is None:(H/'short_closure_lift_verification.json').write_text(json.dumps(report,indent=2)+'\n');print(report);raise SystemExit()
states,edges,ac=result;comps,labels=scc(edges);inside=defaultdict(list)
for e in edges:
 if labels[e['u']]==labels[e['v']]:inside[labels[e['u']]].append(e)
cyclic=[(k,S,inside[k]) for k,S in enumerate(comps) if len(S)>1 or any(e['u']==e['v'] for e in inside[k])]
raw=gzip.decompress((H/'frozen_potential.i64.gz').read_bytes());assert hashlib.sha256(raw).hexdigest()==json.loads((H/'frozen_source_analysis.json').read_text())['potential_sha256'];pi=array.array('q');pi.frombytes(raw)
if sys.byteorder!='little':pi.byteswap()
assert all(e['weight']+pi[states[e['u']][0]]-pi[states[e['v']][0]]==480 for e in edges)
report.update({'patterns':len(patterns),'cyclic_components':[{'vertices':len(S),'edges':len(E)} for _,S,E in cyclic],'all_edges_tight480':True,'scope':'short-window-completed history lift of filtered frozen critical subset only','new_global_bound':None})
if cyclic:
 _,S,E=min(cyclic,key=lambda t:len(t[1]));adj=defaultdict(list)
 for e in E:adj[e['u']].append(e)
 C=shortest_cycle(adj,min(S),maxdepth=10000);assert C and sum(e['weight'] for e in C)==480*len(C);report['mean']='480';report['attaining_cycle']=[{'lift_u':e['u'],'lift_v':e['v'],'source_edge':e['projection'],'weight':e['weight']} for e in C]
else:report['mean']='ACYCLIC'
(H/'short_closure_lift_verification.json').write_text(json.dumps(report,indent=2)+'\n')
with gzip.open(H/'short_closure_lift.json.gz','wt',encoding='utf-8') as f:json.dump({'states':states,'edges':edges},f,separators=(',',':'))
print(json.dumps({k:v for k,v in report.items() if k!='attaining_cycle'},indent=2))
