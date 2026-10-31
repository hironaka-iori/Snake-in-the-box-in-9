"""Sparse reachable product for direction-only forbidden histories.
Unlike edge-ID prefixes, a direction prefix does NOT determine one count state.
"""
from pathlib import Path
from collections import defaultdict,deque
import json,time,gzip,array,sys,hashlib
from compact_history_lift import AC
from probe_critical_cycles import scc,shortest_cycle
H=Path(__file__).resolve().parent

def lift_direction(edges,patterns,state_limit=500000,seconds=40):
 start=time.perf_counter();ac=AC(patterns);adj=defaultdict(list)
 for e in edges:adj[e['u']].append(e)
 nodes=sorted({v for e in edges for v in [e['u'],e['v']]});states=[(v,0) for v in nodes];index={s:i for i,s in enumerate(states)};out=[];cursor=0
 while cursor<len(states):
  if len(states)>state_limit or time.perf_counter()-start>seconds:return None,{'status':'UNKNOWN_BUDGET','states_so_far':len(states),'processed':cursor}
  v,q=states[cursor]
  for e in adj[v]:
   destq=ac.step(q,tuple(e['directions']))
   if ac.bad[destq]:continue
   key=(e['v'],destq)
   if key not in index:index[key]=len(states);states.append(key)
   out.append({'source_edge':len(out),'u':cursor,'v':index[key],'weight':e['weight'],'projection':e['source_edge']})
  cursor+=1
 return (states,out,ac),{'status':'COMPLETE','base_vertices':len(nodes),'lift_vertices':len(states),'lift_edges':len(out),'AC_states':len(ac.next),'seconds':time.perf_counter()-start}

def main():
 base=json.loads((H/'filtered_critical_edges.json').read_text());patterns=[tuple(tuple(w) for w in p) for p in json.loads((H/'direction_patterns.json').read_text())];result,report=lift_direction(base,patterns)
 if result is None:(H/'direction_lift_verification.json').write_text(json.dumps(report,indent=2)+'\n');print(report);return
 states,edges,ac=result;comps,labels=scc(edges);inside=defaultdict(list)
 for e in edges:
  if labels[e['u']]==labels[e['v']]:inside[labels[e['u']]].append(e)
 cyclic=[(k,S,inside[k]) for k,S in enumerate(comps) if len(S)>1 or any(e['u']==e['v'] for e in inside[k])]
 raw=gzip.decompress((H/'frozen_potential.i64.gz').read_bytes());meta=json.loads((H/'frozen_source_analysis.json').read_text());assert hashlib.sha256(raw).hexdigest()==meta['potential_sha256'];pi=array.array('q');pi.frombytes(raw)
 if sys.byteorder!='little':pi.byteswap()
 assert all(e['weight']+pi[states[e['u']][0]]-pi[states[e['v']][0]]==480 for e in edges)
 report.update({'scope':'direction-history product of filtered frozen critical subset only','direction_patterns':len(patterns),'cyclic_SCCs':[{'vertices':len(S),'edges':len(E)} for _,S,E in cyclic],'all_retained_edges_tight_at':480,'new_global_bound':None})
 if cyclic:
  _,S,E=min(cyclic,key=lambda t:len(t[1]));adj=defaultdict(list)
  for e in E:adj[e['u']].append(e)
  C=shortest_cycle(adj,min(S),maxdepth=10000);assert C and sum(e['weight'] for e in C)==480*len(C);report['mean']='480';report['attaining_cycle']=[{'lift_u':e['u'],'lift_v':e['v'],'source_edge':e['projection'],'weight':e['weight']} for e in C]
 else:report['mean']='ACYCLIC_NO_TIGHT_CYCLE';report['source_complete_critical_extraction_reverified_here']=False
 (H/'direction_lift_verification.json').write_text(json.dumps(report,indent=2)+'\n')
 with gzip.open(H/'direction_lift.json.gz','wt',encoding='utf-8') as f:json.dump({'states':states,'edges':edges},f,separators=(',',':'))
 print(json.dumps({k:v for k,v in report.items() if k!='attaining_cycle'},indent=2))
if __name__=='__main__':main()
