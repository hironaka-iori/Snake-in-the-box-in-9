"""Retain only completed exclusions in the variable-crossing construction."""
from pathlib import Path
import collections,hashlib,json
H=Path(__file__).resolve().parents[1]
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):return json.loads(Path(p).read_bytes())
pins={};runs=[]
raw=read(H/'data/regions46.json')
rows={r['id']:dict(id=r['id'],intervals=r['intervals'],status='STATIC_EXCLUDED' if r['status']=='STATIC_EXCLUDED' else 'OPEN') for r in raw['contexts']}
pins[str(H/'data/regions46.json')]=sha(H/'data/regions46.json')
def batch(tag):
    ep=H/'data'/(tag+'-execution.json');rp=H/'data'/(tag+'.json');e=read(ep);j=read(rp)
    assert e['status']=='ACCEPTED_NATIVE_RESULT' and e['exit_code']==0 and e['stop_reason'] is None
    assert all(sha(p)==h for p,h in e['pins'].items()) and sha(rp)==e['result_sha256']
    assert j['witness'] is None and j['source_sha256']==sha(H/'data/regions46.json')
    for r in j['results']:
        assert r['intervals']==raw['contexts'][r['id']]['intervals']
        assert sha(H/'data'/r['model'])==r['model_sha256']
        if r['status']=='INFEASIBLE':assert r['iterations'][-1]['status']=='INFEASIBLE'
    pins[str(ep)]=sha(ep);pins[str(rp)]=sha(rp)
    runs.append(dict(tag=tag,status=j['status'],seconds=j['seconds'],statuses=dict(collections.Counter(r['status'] for r in j['results'])),receipt_sha256=sha(ep),result_sha256=sha(rp)))
    return j
six=batch('six46');initial=batch('free46');counts=batch('counts46');long=batch('counts46-long')
pending={i for i,r in rows.items() if r['status']=='OPEN'}
assert {r['id'] for r in initial['results']}==pending and len(pending)==209
initial_unknown={r['id'] for r in initial['results'] if r['status']!='INFEASIBLE'}
assert {r['id'] for r in counts['results']}<=initial_unknown
assert set(map(int,counts['arguments']['ids'].split(',')))==initial_unknown
second_unknown={r['id'] for r in counts['results'] if r['status']!='INFEASIBLE'}
assert set(map(int,long['arguments']['ids'].split(',')))==second_unknown
assert {r['id'] for r in long['results']}<=second_unknown
for tag,j in [('free46',initial),('counts46',counts),('counts46-long',long)]:
    for r in j['results']:
        assert rows[r['id']]['status']=='OPEN'
        if r['status']=='INFEASIBLE':rows[r['id']].update(status='NATIVE_EXCLUDED',batch=tag,result=r)
        else:rows[r['id']].update(last_status=r['status'],last_batch=tag)
unresolved=[i for i,r in rows.items() if r['status']=='OPEN']
six_unknown=[r['id'] for r in six['results'] if r['status']!='INFEASIBLE']
out=dict(status='COMPLETE_NATIVE_EXCLUSION' if not unresolved else 'PARTIAL_NATIVE_EXCLUSION',round=229,width=46,total_crossings=None,contexts=315,counts=dict(collections.Counter(r['status'] for r in rows.values())),unresolved=unresolved,unresolved_intervals=[rows[i]['intervals'] for i in unresolved],contexts_table=list(rows.values()),six_initial_unknown=six_unknown,six_unresolved_after_free=[i for i in six_unknown if i in unresolved],runs=runs,pins=pins,scope='Any crossing count, fixed bank123 seed and append24, two length-preserving blocks of at most46edges with retained anchors/outside. Initial geometry and completed nativefree/count-strengthened infeasibility only. Strengthened queries depend on the same-context four-crossing cover and only original completed six-crossing results. Unknown/time-limited/unattempted cases remain unresolved. No new snake or global bound; no Lean solver certificates.')
(H/'data/free-summary.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print('VARIABLE_CROSSING_FRONTIER',out['status'],out['counts'],'UNRESOLVED',unresolved)
