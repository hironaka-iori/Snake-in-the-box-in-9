"""Close the fixed two-block family using the eleven terminal visit queries."""
from pathlib import Path
import hashlib,json
H=Path(__file__).resolve().parents[1]
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):return json.loads(Path(p).read_bytes())
prior=read(H/'data/free-summary.json');result=read(H/'data/visits46.json');ex=read(H/'data/visits46-execution.json')
assert ex['status']=='ACCEPTED_NATIVE_RESULT' and ex['stop_reason'] is None
assert all(sha(p)==h for p,h in ex['pins'].items()) and ex['result_sha256']==sha(H/'data/visits46.json')
assert result['status']=='COMPLETE_COVERAGE' and result['witness'] is None
assert sorted(r['id'] for r in result['results'])==prior['unresolved']
new={r['id']:r for r in result['results']}
for r in new.values():
    assert r['status']=='INFEASIBLE' and not r['cycle_cuts']
    assert sha(H/'data'/r['model'])==r['model_sha256']
rows=[]
for row in prior['contexts_table']:
    row=dict(row)
    if row['id'] in new:row.update(status='NATIVE_EXCLUDED',batch='visits46',result=new[row['id']])
    rows.append(row)
assert len(rows)==315 and all(r['status'] in ['STATIC_EXCLUDED','NATIVE_EXCLUDED'] for r in rows)
out=dict(status='COMPLETE_NATIVE_EXCLUSION',round=230,width=46,total_crossings=None,contexts=315,
    counts=dict(STATIC_EXCLUDED=106,PRIOR_NATIVE_EXCLUDED=198,NEW_NATIVE_EXCLUDED=11),unresolved=[],contexts_table=rows,
    pins={str(p):sha(p) for p in [Path(__file__),H/'data/free-summary.json',H/'data/coverage-two46.json',H/'data/coverage46.json',H/'data/visits46.json',H/'data/visits46-execution.json']},
    scope='Every crossing count in fixed bank123 append24 construction, two separated length-preserving blocks at most46edges with retained anchors/outside. Prior304 unrestricted exclusions plus11 newly infeasible visit queries. Same-context2/4/6 exclusions imply>=8 for the final queries. Face-visit inequalities have written extraction plus3 Lean-checked components. Enumeration, data extraction and native contradictions are not end-to-end Lean certified. No new snake or global bound.')
(H/'data/coverage-free46.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print('COMPLETE_ANY_COUNT_FAMILY',len(rows))
