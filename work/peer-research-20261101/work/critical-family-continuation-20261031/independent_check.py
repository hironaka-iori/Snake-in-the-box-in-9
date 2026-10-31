from pathlib import Path
import json,hashlib
H=Path(__file__).resolve().parent;report=json.loads((H/'review.json').read_text());raw=(H.parent/'global-cycle-compression-20261031/critical_edges_frozen.json').read_bytes();assert hashlib.sha256(raw).hexdigest()==report['source_sha256'];records={e['source_edge']:e for e in json.loads(raw)}
def canonical(word):
 labels={};out=[]
 for a in word:
  if a not in labels:labels[a]=len(labels)
  out.append(labels[a])
 return out
def induced(word):
 verts=[frozenset()]
 for a in word:verts.append(verts[-1]^{a})
 return all(len(a^b)>1 for i,a in enumerate(verts) for j,b in enumerate(verts) if j>i+1)
checked=0;rows=[]
for row in report['small_cycle_results']:
 pattern=row['forbidden_9edge_pattern'];frontier=[records[pattern[0]]['directions']]
 assert induced(frontier[0]);survivor=None
 for level in row['levels']:
  w=records[pattern[level['edge_count']-1]]['directions'];nxt=[]
  for p in frontier:
   for direction in range(9):
    checked+=1;q=p+[direction]
    if canonical(q[-9:])==w and induced(q):nxt.append(q)
  assert len(nxt)==level['alive'];digest=hashlib.sha256(json.dumps(sorted(nxt),separators=(',',':')).encode()).hexdigest();assert digest==level['alive_directions_sha256']
  if nxt:survivor=nxt[0]
  frontier=nxt
 assert not frontier and len(survivor)==16 and induced(row['longest_survivor_directions'])
 rows.append({'component':row['component'],'phase_vertex':row['phase_vertex'],'forbidden_graph_edges':9,'longest_realizable_direction_prefix':16,'full_frontier_hashes_match':True})
out={'status':'PASS','source_sha256':report['source_sha256'],'independent_method':'try all nine next coordinates; canonicalize full nine-direction window; full pairwise set-symmetric-difference path check','coordinate_trials':checked,'phases':rows,'old_six_component_family_only':True,'current_eight_case_graph_covered':False,'Lean_checked':False,'new_global_bound':None}
(H/'independent_check.json').write_text(json.dumps(out,indent=2));print(json.dumps({k:v for k,v in out.items() if k!='phases'},indent=2))
