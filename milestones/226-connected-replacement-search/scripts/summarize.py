"""Freeze the native43 cover, remaining44 cases and shared Q8 construction target."""
from pathlib import Path
import hashlib,json,collections
H=Path(__file__).resolve().parents[1];R=H.parents[1]
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):return json.loads(Path(p).read_bytes())
def save(p,j):p.write_text(json.dumps(j,indent=2)+'\n',encoding='utf-8')
runs={}
for p in sorted((H/'data').glob('*-execution.json')):
    e=read(p)
    if 'resource_gate' not in e:continue
    assert e['status']=='ACCEPTED_NATIVE_RESULT' and e['exit_code']==0 and e['stop_reason'] is None
    assert all(sha(q)==v for q,v in e['pins'].items())
    tag=p.name.removesuffix('-execution.json');q=H/'data'/(tag+'.json')
    if not q.exists():q=H/'data'/tag/'result.json'
    j=read(q);assert sha(q)==e['result_sha256']
    if 'checkpoint_sha256' in j:assert sha(q.with_name('checkpoint.json'))==j['checkpoint_sha256']
    runs[tag]=dict(status=j['status'],result_sha256=sha(q),execution_sha256=sha(p),seconds=j['seconds'])
parent=R/'milestones/224-cross-block-reconnections/data/combined44.json';combined={r['id']:dict(r) for r in read(parent)['contexts']}
boundary=read(H/'data/boundary44.json');assert len(boundary['results'])==92
for r in boundary['results']:
    assert combined[r['id']]['status']=='UNKNOWN'
    combined[r['id']]=dict(r,latest_query='boundary44')
ports={}
for tag in ['port202-224','port202-232','ports44-224','ports44-232']:
    j=read(H/'data'/(tag+'.json'));port=j['arguments']['first_port']
    for r in j['results']:ports.setdefault(r['id'],{})[port]=dict(status=r['status'],tag=tag)
catalogue=read(H/'data/upper-suffixes.json');assert set(ports)=={r['id'] for r in catalogue['contexts']}
for ident,choices in ports.items():
    assert set(choices)=={224,232}
    if all(x['status']=='INFEASIBLE' for x in choices.values()):combined[ident].update(status='PORT_COVER_EXCLUDED',port_results=choices)
    else:combined[ident]['port_results']=choices
unknown=sorted(i for i,r in combined.items() if r['status']=='UNKNOWN')
assert len(combined)==301 and len(unknown)==42
save(H/'data/combined44.json',dict(contexts=[combined[i] for i in sorted(combined)],unresolved=unknown,counts=dict(collections.Counter(r['status'] for r in combined.values())),pins={str(parent):sha(parent),str(H/'data/boundary44.json'):sha(H/'data/boundary44.json')},scope='Old native44 exclusions plus boundary/face constraints justified by native43closure and two-port covers. No Lean replay of solver contradictions.'))
shared=sorted(i for i,p in ports.items() if p[224]['status']=='UNKNOWN');assert shared==[194,195,196,197,198,199,201]
raw=read(H/'data/regions44.json');domain=[v for v in raw['contexts'][shared[0]]['parts'][0]['allowed'] if v<256]
assert len(domain)==109 and all([v for v in raw['contexts'][i]['parts'][0]['allowed'] if v<256]==domain for i in shared)
plan=dict(status='PREPARED_SHARED_SEARCH',contexts=shared,first_lower_domain=domain,first_lower_anchors=[18,224],first_lower_edges=43,first_upper_suffix=[480],first_interval=[4,48],second_crossings=2,source_sha256=sha(H/'data/regions44.json'),context_rows=[raw['contexts'][i] for i in shared],scope='All seven remaining odd-first-crossing contexts require this same Q8 path problem. Search a common prefix once and prune it only when every second context is impossible. At full first path, try each surviving second context and audit the entire193vertexsnake. This plan has not been executed.')
save(H/'data/shared-q8-plan.json',plan)
summary=dict(round=226,status='PROGRESS',complete_through=43,width43_contexts=294,width43_unresolved=0,width44_contexts=301,width44_initial_open=92,boundary_new_exclusions=46,port_new_exclusions=4,width44_unresolved=unknown,shared_q8_contexts=shared,runs=runs,new_q9_record=False,new_global_bound=False,solver_contradictions_lean_checked=False)
save(H/'data/search-summary.json',summary)
print('SUMMARY',len(unknown),'open44contexts;',len(shared),'share one109vertexQ8domain')
