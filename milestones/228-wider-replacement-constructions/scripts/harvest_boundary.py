"""Preserve only completed queries from the resource-interrupted batch."""
from pathlib import Path
import collections,hashlib,json
H=Path(__file__).resolve().parents[1]
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):return json.loads(Path(p).read_bytes())
ep=H/'data/boundary45-execution.json';rp=H/'data/boundary45.json';sp=H/'data/regions45.json'
e=read(ep);j=read(rp);raw=read(sp)
assert e['status']=='INTERRUPTED' and e['stop_reason']=='LOW_FREE_MEMORY' and e['exit_code'] is not None
assert sha(rp)==e['result_sha256'] and all(sha(p)==h for p,h in e['pins'].items())
assert sha(sp)==j['source_sha256'] and sha(H/'scripts/joint_boundary.py')==j['script_sha256']
rows={r['id']:dict(r) for r in raw['contexts']};recorded=[]
for r in j['results']:
    assert rows[r['id']]['status']=='PENDING'
    assert sha(H/'data'/r['model'])==r['model_sha256']
    if r['status']=='INFEASIBLE':
        assert r['iterations'][-1]['status']=='INFEASIBLE' and 'seconds' in r
        assert len(r['iterations'])==1 and not r['cycle_cuts']
        rows[r['id']].update(status='PARTIAL_BATCH_EXCLUDED',native_result=r)
        recorded.append(r['id'])
    else:rows[r['id']]['last_native_status']=r['status']
for r in rows.values():
    if r['status']=='PENDING':r['status']='OPEN'
out=dict(status='PARTIAL_TERMINAL_RESULTS_RECORDED',width=45,contexts=list(rows.values()),accepted_completed_query_ids=recorded,counts=dict(collections.Counter(r['status'] for r in rows.values())),pins={str(p):sha(p) for p in [ep,rp,sp,Path(__file__)]},scope='Only final INFEASIBLE rows saved before a later query was terminated are carried forward. The batch itself is not accepted as complete; its running, unknown and unattempted cases stay open. Every accepted row has one terminal iteration, no cycle cut, a complete model and unchanged input/source pins. Native solver evidence, no Lean contradiction certificate.')
(H/'data/baseline45.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps(dict(completed_exclusions=len(recorded),counts=out['counts'])),flush=True)
