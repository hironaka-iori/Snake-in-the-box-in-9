"""Merge distinct finite-search records without counting a timeout as exclusion."""
from pathlib import Path
import collections,hashlib,json,subprocess
H=Path(__file__).resolve().parents[1];R=H.parents[1]
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
records={}
for tag in ['pair33','pair33-free','pair44','pair44-flow']:
    p=H/'data'/(tag+'.json');d=json.loads(p.read_bytes());run=json.loads((H/'data'/(tag+'-execution.json')).read_bytes())
    assert run['status']=='ACCEPTED_NATIVE_RESULT' and run['exit_code']==0 and run['stop_reason'] is None
    assert sha(p)==run['result_sha256'] and all(sha(p)==v for p,v in run['pins'].items())
    assert d['status']=='COMPLETE_COVERAGE' and len(d['results'])==d['total_contexts']
    assert len({r['id'] for r in d['results']})==len(d['results'])
    for row in d['results']:
        assert row['status'] in ['STATIC_EXCLUDED','INFEASIBLE','UNKNOWN','TIME_LIMIT']
        if 'model' in row:assert sha(H/'data'/row['model'])==row['model_sha256']
    records[tag]=d
combined={r['id']:dict(r,latest_query='pair44') for r in records['pair44']['results']}
for row in records['pair44-flow']['results']:
    assert combined[row['id']]['status'] in ['UNKNOWN','TIME_LIMIT']
    combined[row['id']]=dict(row,latest_query='pair44-flow')
assert set(combined)==set(range(301))
summary=dict(round=224,previous_goal_turn='PROGRESS',interval=[191,233],new_witness=False,new_global_bound=False,
    runs={tag:dict(seconds=d['seconds'],statuses=d['statuses'],total=d['total_contexts'],cycles=sum(len(r.get('cycle_cuts',[])) for r in d['results']),result_sha256=sha(H/'data'/(tag+'.json')),execution_sha256=sha(H/'data'/(tag+'-execution.json'))) for tag,d in records.items()},
    short_family_excluded=all(r['status'] in ['STATIC_EXCLUDED','INFEASIBLE'] for r in records['pair33-free']['results']),
    long_family_statuses=dict(collections.Counter(r['status'] for r in combined.values())),
    unresolved44=[i for i,r in sorted(combined.items()) if r['status'] in ['UNKNOWN','TIME_LIMIT']],
    biconnected_refinement=dict(contexts=92,removed_vertices=0,new_exclusions=0,native_rerun=False),
    scope='The33-edge numerical exclusion does not use mutualcontact or the bank-closure premise. Native solver contradictions and finite data have not been fully transferred to Lean. The44-edge table combines distinct contextIDs, retaining unresolved cases.',
    input_pins={str(p.relative_to(R)):sha(p) for p in [H/'data/regions.json',H/'data/regions33-free.json',H/'data/regions44.json',H/'data/regions44-flow.json']})
(H/'data/search-summary.json').write_text(json.dumps(summary,indent=2)+'\n',encoding='utf-8')
(H/'data/combined44.json').write_text(json.dumps(dict(contexts=[combined[i] for i in range(301)],scope=summary['scope']),indent=2)+'\n',encoding='utf-8')
print(json.dumps(summary),flush=True)
