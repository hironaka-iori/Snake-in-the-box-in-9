from pathlib import Path
import json,collections,hashlib
H=Path(__file__).resolve().parent
D=json.loads((H.parent/'global-cycle-compression-20261031/critical_edges_frozen.json').read_text());kept=json.loads((H/'filtered_critical_edges.json').read_text());cases=json.loads((H/'current_cases.json').read_text());current=json.loads((H.parent/'global-cycle-compression-20261031/upstream_proved_model.json').read_text());applied=set(current['applied_cases']);cases=[x for x in cases if x['number'] in applied]
def canonical(w):
 out=[];seen=[]
 for a in w:
  if a not in seen:seen.append(a)
  out.append(seen.index(a))
 return out
def hit(e,c):
 for start in [2,3,4]:
  for backwards in [False,True]:
   word=e['directions'][start:start+5];locations=list(range(start+1,start+5))
   if backwards:word=word[::-1];locations=locations[::-1]
   if canonical(word)!=c['dirs']:continue
   inside=True
   for pos,(lo,hi) in zip(locations,c['bounds']):
    bucket=e['counts'][pos-3];possible=[bucket] if bucket<6 else list(range(6,22))
    statuses=[lo<=x<=hi for x in possible]
    assert all(statuses) or not any(statuses),'partial bucket interval'
    if not all(statuses):inside=False
   if inside:return True
 return False
removed=collections.defaultdict(set);want=[]
for e in D:
 hits=[c['number'] for c in cases if hit(e,c)]
 for c in hits:removed[c].add(e['source_edge'])
 if not hits:want.append(e)
assert want==kept and len(kept)==18737
assert len(removed[7203])==116 and len(removed[7216])==34 and len(removed[7203]&removed[7216])==22
small={e['source_edge'] for e in D if e['component'] in [262705,286269,283106]};assert small<={e['source_edge'] for e in kept}
# Independent literal-coordinate checker for all specifically REFUTED probe phases.
probe=json.loads((H/'critical_cycle_probes.json').read_text());byid={e['source_edge']:e for e in kept};nproof=trials=0;maxstates=0;reviewed=[]
for row in probe['candidate_cycles']:
 if row['status']!='REFUTED':continue
 C=[byid[i] for i in row['source_edge_ids']];assert all(e['v']==C[(j+1)%len(C)]['u'] for j,e in enumerate(C))
 first=C[0]['directions'];v=[0]
 for a in first:v.append(v[-1]^(1<<a))
 assert all((a^b).bit_count()>1 for i,a in enumerate(v) for j,b in enumerate(v) if j>i+1)
 frontier=[(first,v)]
 for count in range(2,row['forbidden_edges']+1):
  nxt=[];wanted=C[(count-1)%len(C)]['directions']
  for dirs,verts in frontier:
   for a in range(9):
    trials+=1;newdirs=dirs+[a]
    if canonical(newdirs[-9:])!=wanted:continue
    x=verts[-1]^(1<<a)
    if all((x^z).bit_count()>1 for z in verts[:-1]):nxt.append((newdirs,verts+[x]))
  frontier=nxt;maxstates=max(maxstates,len(nxt));assert len(nxt)<1000000
 assert not frontier,(row['source_edge_ids'],row['forbidden_edges']);nproof+=1;reviewed.append({'source_edge_ids':row['source_edge_ids'],'forbidden_edges':row['forbidden_edges']})
out={'status':'PASS','filtered_records':len(kept),'removed_unique':len(D)-len(kept),'hits7203':len(removed[7203]),'hits7216':len(removed[7216]),'hit_intersection':22,'small_cycle_edges_all_retained':len(small),'bucket6_semantics':'entire integer interval 6..21 checked; no partial inclusion','explicit_REFUTED_histories_independently_checked':nproof,'coordinate_trials':trials,'largest_uncompressed_frontier':maxstates,'STATE_LIMIT_and_DEPTH_LIMIT_not_refutations':True,'new_global_bound':None,'source_hashes':{n:hashlib.sha256((H/n).read_bytes()).hexdigest() for n in ['filtered_critical_edges.json','critical_cycle_probes.json','probe_critical_cycles.py','filter_current_cases.py']},'reviewed_patterns':reviewed}
(H/'filter_and_probe_review.json').write_text(json.dumps(out,indent=2));print(json.dumps({k:v for k,v in out.items() if k!='reviewed_patterns'},indent=2))
