"""Apply the standalone checked count-window exclusion to the explicit subgraph."""
from pathlib import Path
from collections import defaultdict
import json,gzip
from direction_history_lift import lift_direction
from probe_critical_cycles import scc,shortest_cycle
H=Path(__file__).resolve().parent

def excluded(edge,rule):
 if edge['directions']!=rule['directions']:return False
 for position,(lo,hi) in zip(rule['count_positions'],rule['bounds']):
  bucket=edge['counts'][position-3];a,b=(6,21) if bucket==6 else (bucket,bucket)
  if not lo<=a<=b<=hi:return False
 return True

def main():
 base=json.loads((H/'filtered_critical_edges.json').read_text());rule=json.loads((H/'count_window_certificate/manifest.json').read_text());removed=[e for e in base if excluded(e,rule)];kept=[e for e in base if not excluded(e,rule)];(H/'count_refined_critical_edges.json').write_text(json.dumps(kept,separators=(',',':'))+'\n');patterns=[tuple(tuple(w) for w in p) for p in json.loads((H/'short_closure_patterns.json').read_text())];result,report=lift_direction(kept,patterns,state_limit=250000,seconds=30)
 if result is None:raise RuntimeError('lift not complete')
 states,edges,_=result;cs,labels=scc(edges);inside=defaultdict(list)
 for e in edges:
  if labels[e['u']]==labels[e['v']]:inside[labels[e['u']]].append(e)
 cyclic=[(k,S,inside[k]) for k,S in enumerate(cs) if len(S)>1 or any(e['u']==e['v'] for e in inside[k])]
 out={'scope':'one new checked count-window rule on filtered frozen subgraph plus431 existing direction cuts','removed_base_edges':len(removed),'removed_source_edge_ids':[e['source_edge'] for e in removed],'retained_base_edges':len(kept),**report,'cyclic_SCCs':[{'nodes':len(S),'edges':len(E)} for _,S,E in cyclic],'new_global_bound':None,'Lean_checked':False}
 if cyclic:
  _,S,E=min(cyclic,key=lambda t:len(t[1]));adj=defaultdict(list)
  for e in E:adj[e['u']].append(e)
  C=shortest_cycle(adj,min(S),10000);assert C and sum(e['weight'] for e in C)==480*len(C);out['attaining_cycle']=[{'source_edge':e['projection'],'weight':e['weight'],'u':e['u'],'v':e['v']} for e in C];out['mean']='480'
 (H/'count_rule_effect.json').write_text(json.dumps(out,indent=2)+'\n')
 with gzip.open(H/'count_refined_lift.json.gz','wt') as f:json.dump({'states':states,'edges':edges},f,separators=(',',':'))
 print(json.dumps({k:v for k,v in out.items() if k not in ['removed_source_edge_ids','attaining_cycle']},indent=2))
if __name__=='__main__':main()
