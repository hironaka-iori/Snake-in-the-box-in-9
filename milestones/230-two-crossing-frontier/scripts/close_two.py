"""Assemble the native exact-two cover without changing older evidence."""
from pathlib import Path
import hashlib,json
H=Path(__file__).resolve().parents[1]
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):return json.loads(Path(p).read_bytes())
lower=read(H/'data/lower-pairs.json');prior=read(H/'data/free-summary.json')
result=read(H/'data/two-pairs/result.json');execution=read(H/'data/two-pairs-execution.json')
assert lower['total_crossings']==2 and not lower['unsupported']
assert execution['status']=='ACCEPTED_NATIVE_RESULT' and execution['stop_reason'] is None
assert all(sha(p)==h for p,h in execution['pins'].items())
assert execution['result_sha256']==sha(H/'data/two-pairs/result.json')
assert all(sha(p)==h for p,h in lower['pins'].items())
assert all(sha(p)==h for p,h in prior['pins'].items())
assert lower['representatives']==list(range(15))
assert sorted(r['id'] for r in result['results'])==list(range(15))
for r in result['results']:
    assert r['status']=='INFEASIBLE' and not r['cycle_cuts']
    assert sha(H/'data/two-pairs'/f"model-{r['id']}.pbtxt")==r['model_sha256']
assert sorted(r['context'] for r in lower['contexts'])==prior['unresolved']
assert all(r['configurations'] for r in lower['contexts'])
rows=[]
for row in prior['contexts_table']:
    if row['id'] in prior['unresolved']:
        c=next(c for c in lower['contexts'] if c['context']==row['id'])
        rows.append(dict(id=row['id'],intervals=row['intervals'],status='EXACT_TWO_NATIVE_EXCLUDED',configurations=c['configurations']))
    else:rows.append(dict(id=row['id'],intervals=row['intervals'],status='PRIOR_UNRESTRICTED_EXCLUDED'))
out=dict(status='COMPLETE_NATIVE_EXCLUSION',round=230,width=46,total_crossings=2,contexts=315,contexts_table=rows,
    pins={str(p):sha(p) for p in [Path(__file__),H/'data/lower-pairs.json',H/'data/free-summary.json',H/'data/two-pairs/result.json',H/'data/two-pairs-execution.json']},
    scope='Native exact-two exclusion for fixed bank123 append24, retained anchors/outside, two length-preserving blocks at most46edges. Prior304 unrestricted exclusions plus15 complete reduced queries over remaining11contexts. No boundary-change cut and no Lean solver certificate.')
(H/'data/coverage-two46.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print('EXACT_TWO_COMPLETE',len(rows))
