"""Assemble the exact four-crossing width-46 native cover."""
from pathlib import Path
import collections,hashlib,json
H=Path(__file__).resolve().parents[1]
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):return json.loads(Path(p).read_bytes())
def save(p,j):p.write_text(json.dumps(j,indent=2)+'\n',encoding='utf-8')
pins={};runs=[]
def pinned(p):
    j=read(p);pins[str(p)]=sha(p)
    assert all(sha(q)==h for q,h in j.get('pins',{}).items())
    return j
base=pinned(H/'data/baseline46.json');lower=pinned(H/'data/boundary-lower-pairs.json');transfer=pinned(H/'data/task-transfer.json')
rows={r['id']:dict(r) for r in base['contexts']}
assert len(rows)==315 and base['counts']=={'STATIC_EXCLUDED':106,'OPEN':209}
def batch(tag,reduced):
    ep=H/'data'/(tag+'-execution.json');rp=H/'data'/tag/'result.json' if reduced else H/'data'/(tag+'.json')
    e=pinned(ep);j=pinned(rp)
    assert e['status']=='ACCEPTED_NATIVE_RESULT' and e['exit_code']==0 and e['stop_reason'] is None
    assert sha(rp)==e['result_sha256'] and j['witness'] is None
    assert j['status'] in ['COMPLETE_QUERY_BATCH','COMPLETE_COVERAGE']
    for r in j['results']:
        p=rp.parent/f'model-{r["id"]}.pbtxt' if reduced else H/'data'/r['model']
        assert sha(p)==r['model_sha256']
        if r['status']=='INFEASIBLE':assert len(r['iterations'])==1 and r['iterations'][0]['status']=='INFEASIBLE' and not r['cycle_cuts']
    runs.append(dict(tag=tag,status=j['status'],seconds=j['seconds'],statuses=dict(collections.Counter(r['status'] for r in j['results'])),receipt_sha256=sha(ep),result_sha256=sha(rp)))
    return j
first=batch('reduced46',True);retry=batch('reduced46-long',True);direct=batch('complex46',False)
assert {r['id'] for r in first['results']}==set(transfer['pending']) and len(first['results'])==495
unknown={r['id'] for r in first['results'] if r['status']!='INFEASIBLE'}
assert unknown=={r['id'] for r in retry['results']} and len(unknown)==8
assert all(r['status']=='INFEASIBLE' for r in retry['results'])
completed={r['id']:dict(batch='reduced46',result=r) for r in first['results'] if r['status']=='INFEASIBLE'}
completed.update({r['id']:dict(batch='reduced46-long',result=r) for r in retry['results']})
completed.update({int(i):dict(batch='PRIOR_NATIVE_TRANSFER',transfer=r) for i,r in transfer['transfers'].items()})
mapping={i:lower['dominated'].get(str(g[0]),g[0]) for g in lower['exact_groups'] for i in g}
assert set(mapping)==set(range(886)) and set(mapping.values())==set(completed) and len(completed)==496
cover=[]
for r in lower['contexts']:
    ident=r['context'];assert rows[ident]['status']=='OPEN'
    reps=sorted({mapping[i] for i in r['configurations']})
    assert all(i in completed for i in reps)
    entry=dict(context=ident,original_configurations=r['original_configurations'],configurations=r['configurations'],representatives=reps)
    rows[ident].update(status='BOUNDARY_TEMPLATE_EXCLUDED' if not reps else 'REDUCED_PAIR_EXCLUDED',cover=entry);cover.append(entry)
assert len(cover)==185 and sum(not r['representatives'] for r in cover)==89
assert {r['context'] for r in lower['unsupported']}=={r['id'] for r in direct['results']} and len(direct['results'])==24
for r in direct['results']:
    assert rows[r['id']]['status']=='OPEN' and r['status']=='INFEASIBLE'
    rows[r['id']].update(status='DIRECT_PAIR_EXCLUDED',native_result=r)
assert not any(r['status']=='OPEN' for r in rows.values())
counts=dict(collections.Counter(r['status'] for r in rows.values()))
scope='All315 maximal width46 contexts: fixed normalized bank123, append24, two length-preserving replacements retaining outside positions and anchors, exactlyfour bit8crossings. The boundary cut depends on complete native45closure. Smaller blocks included by padding. Static preparation, upper enumeration, transfer assembly and solver contradictions are native, not Lean-certified. No new snake or global bound. This cover says nothing about six-crossing replacements.'
out=dict(status='COMPLETE_NATIVE_EXCLUSION',round=229,width=46,contexts=315,counts=counts,contexts_table=[rows[i] for i in sorted(rows)],reduced_cover=cover,configuration_map=mapping,representative_results=completed,pins=pins,scope=scope)
save(H/'data/coverage46.json',out)
save(H/'data/search-summary.json',dict(round=229,status='PROGRESS',complete_through=46,width46_contexts=315,width46_unresolved=[],counts=counts,reduced_contexts=185,empty_reduced_contexts=89,reduced_configurations=886,reduced_representatives=496,reused_representatives=1,new_reduced_queries=495,reduced_initial_unknown=8,direct_queries=24,current_terminal_infeasible_queries=519,new_q9_record=False,new_global_bound=False,runs=runs,coverage_sha256=sha(H/'data/coverage46.json'),scope=scope))
print('COMPLETE_NATIVE_WIDTH46_COVER',len(rows),counts)
