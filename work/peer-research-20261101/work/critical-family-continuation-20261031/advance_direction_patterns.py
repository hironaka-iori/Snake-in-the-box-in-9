"""Bounded direction-history separation; preserve the reviewed 63-pattern snapshot."""
from pathlib import Path
from collections import defaultdict
import json,time,gzip
from direction_history_lift import lift_direction
from probe_critical_cycles import scc,shortest_cycle,realize
H=Path(__file__).resolve().parent

def minimize(P):
 out=[]
 for p in sorted(set(P),key=lambda p:(len(p),p)):
  if not any(any(p[j:j+len(q)]==q for j in range(len(p)-len(q)+1)) for q in out):out.append(p)
 return out

def main():
 start=time.perf_counter();base=json.loads((H/'filtered_critical_edges.json').read_text());byid={e['source_edge']:e for e in base};patterns=[tuple(tuple(w) for w in p) for p in json.loads((H/'direction_patterns.json').read_text())];rounds=[];accepted=[];unresolved=[];last=None;status='ROUND_LIMIT'
 for iteration in range(24):
  if time.perf_counter()-start>=30:status='WALL_BUDGET';break
  result,stat=lift_direction(base,patterns,state_limit=250000,seconds=8)
  if result is None:status='LIFT_BUDGET';break
  states,edges,ac=result;comps,labels=scc(edges);inside=defaultdict(list)
  for e in edges:
   if labels[e['u']]==labels[e['v']]:inside[labels[e['u']]].append(e)
  cyclic=sorted([(k,S,inside[k]) for k,S in enumerate(comps) if len(S)>1 or any(e['u']==e['v'] for e in inside[k])],key=lambda x:len(x[1]));last=(states,edges,patterns[:],cyclic)
  row={'iteration':iteration,'patterns':len(patterns),'states':len(states),'edges':len(edges),'cyclic_components':[{'states':len(S),'edges':len(E)} for _,S,E in cyclic]};rounds.append(row);print(json.dumps(row),flush=True)
  if not cyclic:status='EXPLICIT_TIGHT_SUBGRAPH_ACYCLIC';break
  new=None
  for k,S,E in cyclic:
   adj=defaultdict(list)
   for e in E:adj[e['u']].append(e)
   vs=sorted(S)
   for root in [vs[j*(len(vs)-1)//3] for j in range(4)]:
    C=shortest_cycle(adj,root,maxdepth=64)
    if not C:continue
    projected=[byid[e['projection']] for e in C];r=realize(projected,max_edges=72,max_states=20000)
    if r['status']=='REFUTED':
     count=r['forbidden_edges'];new=tuple(tuple(projected[j%len(projected)]['directions']) for j in range(count));accepted.append({'iteration':iteration,'cycle_source_ids':[e['source_edge'] for e in projected],'forbidden_directions':[list(w) for w in new],'geometry_check':r});break
    unresolved.append({'iteration':iteration,'cycle_source_ids':[e['source_edge'] for e in projected],'geometry_check':r})
   if new:break
  if not new:status='SELECTED_GEOMETRY_PROBES_UNRESOLVED';break
  patterns=minimize(patterns+[new])
 assert last is not None
 states,edges,active,cyclic=last
 # Active rules correspond exactly to the last COMPLETE built graph; a pending rule is separate.
 with gzip.open(H/'direction_lift_extended.json.gz','wt',encoding='utf-8') as f:json.dump({'states':states,'edges':edges},f,separators=(',',':'))
 (H/'direction_patterns_extended.json').write_text(json.dumps([[list(w) for w in p] for p in active],indent=2)+'\n')
 out={'status':status,'scope':'bounded continuation on filtered frozen critical subset','rounds':rounds,'accepted_geometry_rules':accepted,'unresolved_probes':unresolved,'active_patterns':len(active),'pending_patterns':len(patterns),'elapsed_seconds':time.perf_counter()-start,'global_bound':None}
 (H/'direction_extension_report.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items() if k not in ['rounds','accepted_geometry_rules','unresolved_probes']},indent=2))
if __name__=='__main__':main()
