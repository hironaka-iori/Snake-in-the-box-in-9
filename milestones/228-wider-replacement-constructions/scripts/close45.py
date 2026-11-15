"""Assemble the literal width-45 cover, preserving native evidence scope."""
from pathlib import Path
import collections, hashlib, json
H=Path(__file__).resolve().parents[1]
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p): return json.loads(Path(p).read_bytes())
def save(p,j): p.write_text(json.dumps(j,indent=2)+'\n',encoding='utf-8')
pins={};runs=[]
def pinned(p):
    j=read(p);pins[str(p)]=sha(p)
    for q,h in j.get('pins',{}).items(): assert sha(q)==h,q
    return j
base=pinned(H/'data/baseline45.json');lower=pinned(H/'data/boundary-lower-pairs.json')
rows={r['id']:dict(r) for r in base['contexts']}
assert len(rows)==308 and base['counts']=={'STATIC_EXCLUDED':107,'PARTIAL_BATCH_EXCLUDED':34,'OPEN':167}
def batch(tag,reduced):
    ep=H/'data'/(tag+'-execution.json');rp=H/'data'/tag/'result.json' if reduced else H/'data'/(tag+'.json')
    e=pinned(ep);j=pinned(rp)
    assert e['status']=='ACCEPTED_NATIVE_RESULT' and e['exit_code']==0 and e['stop_reason'] is None
    assert sha(rp)==e['result_sha256'] and j['witness'] is None
    assert j['status'] in ['COMPLETE_QUERY_BATCH','COMPLETE_COVERAGE']
    for r in j['results']:
        model=rp.parent/f'model-{r["id"]}.pbtxt' if reduced else H/'data'/r['model']
        assert sha(model)==r['model_sha256']
        if r['status']=='INFEASIBLE':
            assert len(r['iterations'])==1 and r['iterations'][0]['status']=='INFEASIBLE' and not r['cycle_cuts']
    runs.append(dict(tag=tag,status=j['status'],seconds=j['seconds'],statuses=dict(collections.Counter(r['status'] for r in j['results'])),receipt_sha256=sha(ep),result_sha256=sha(rp)))
    return j
first=batch('reduced45',True);retry=batch('reduced45-long',True);direct=batch('complex45',False)
assert {r['id'] for r in first['results']}==set(lower['representatives']) and len(first['results'])==331
unknown={r['id'] for r in first['results'] if r['status']!='INFEASIBLE'}
assert unknown=={r['id'] for r in retry['results']} and len(unknown)==10
assert all(r['status']=='INFEASIBLE' for r in retry['results'])
completed={r['id']:dict(batch='reduced45',result=r) for r in first['results'] if r['status']=='INFEASIBLE'}
completed.update({r['id']:dict(batch='reduced45-long',result=r) for r in retry['results']})
mapping={i:lower['dominated'].get(str(g[0]),g[0]) for g in lower['exact_groups'] for i in g}
assert set(mapping)==set(range(672)) and set(mapping.values())==set(completed)
cover=[]
for r in lower['contexts']:
    ident=r['context'];assert rows[ident]['status']=='OPEN'
    reps=sorted({mapping[i] for i in r['configurations']})
    assert all(i in completed for i in reps)
    entry=dict(context=ident,original_configurations=r['original_configurations'],configurations=r['configurations'],representatives=reps)
    status='BOUNDARY_TEMPLATE_EXCLUDED' if not reps else 'REDUCED_PAIR_EXCLUDED'
    rows[ident].update(status=status,cover=entry);cover.append(entry)
assert len(cover)==154 and sum(not r['representatives'] for r in cover)==69
unsupported={r['context'] for r in lower['unsupported']}
assert unsupported=={r['id'] for r in direct['results']} and len(unsupported)==13
for r in direct['results']:
    assert rows[r['id']]['status']=='OPEN' and r['status']=='INFEASIBLE'
    rows[r['id']].update(status='DIRECT_PAIR_EXCLUDED',native_result=r)
assert not any(r['status']=='OPEN' for r in rows.values())
interrupted=pinned(H/'data/boundary45-execution.json')
assert interrupted['status']=='INTERRUPTED' and interrupted['stop_reason']=='LOW_FREE_MEMORY'
counts=dict(collections.Counter(r['status'] for r in rows.values()))
scope='All308 maximal width45 contexts of fixed normalized bank123, append24, two length-preserving replacements retaining outside indices and anchors, exactly four bit8crossings. The boundary cut depends on the complete native44cover. Static preparation, upper enumeration, transfer assembly and solver contradictions are native, not Lean certified. Padding covers smaller blocks. No global upper bound or new witness.'
out=dict(status='COMPLETE_NATIVE_EXCLUSION',round=228,width=45,contexts=308,counts=counts,contexts_table=[rows[i] for i in sorted(rows)],reduced_cover=cover,configuration_map=mapping,representative_results=completed,pins=pins,scope=scope)
save(H/'data/coverage45.json',out)
save(H/'data/search-summary.json',dict(round=228,status='PROGRESS',complete_through=45,width45_contexts=308,width45_unresolved=[],counts=counts,reduced_contexts=154,empty_reduced_contexts=69,reduced_configurations=672,reduced_queries=331,reduced_initial_unknown=10,direct_queries=13,partial_batch_exclusions=34,all_current_terminal_infeasible_queries=378,new_q9_record=False,new_global_bound=False,runs=runs,interrupted_initial_batch=dict(status=interrupted['status'],reason=interrupted['stop_reason'],accepted_terminal_rows=34),coverage_sha256=sha(H/'data/coverage45.json'),scope=scope))
print('COMPLETE_NATIVE_WIDTH45_COVER',len(rows),counts)
