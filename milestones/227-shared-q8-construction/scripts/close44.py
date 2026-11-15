"""Assemble the exact native cover of all301 width44 contexts."""
from pathlib import Path
import hashlib,json
H=Path(__file__).resolve().parents[1];R=H.parents[1]
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):return json.loads(Path(p).read_bytes())
def save(p,j):p.write_text(json.dumps(j,indent=2)+'\n',encoding='utf-8')
pins={};runs=[]
for tag in ['shared120','reduced-pairs','remaining-pairs']:
    ep=H/'data'/(tag+'-execution.json');rp=H/'data'/tag/'result.json';e=read(ep);j=read(rp)
    assert e['status']=='ACCEPTED_NATIVE_RESULT' and e['exit_code']==0 and e['stop_reason'] is None
    assert all(sha(p)==h for p,h in e['pins'].items());assert sha(rp)==e['result_sha256']
    if 'checkpoint_sha256' in j:assert sha(rp.with_name('checkpoint.json'))==j['checkpoint_sha256']
    pins[str(ep)]=sha(ep);pins[str(rp)]=sha(rp)
    runs.append(dict(tag=tag,status=j['status'],seconds=j['seconds'],execution_sha256=sha(ep),result_sha256=sha(rp)))
priorpath=R/'milestones/226-connected-replacement-search/data/combined44.json';prior=read(priorpath)
combined={r['id']:dict(r) for r in prior['contexts']};assert len(combined)==301
pins[str(priorpath)]=sha(priorpath)
initialpath=H/'data/companions.json';initial=read(initialpath)
generalpath=H/'data/remaining-companions.json';general=read(generalpath)
for path,j in [(initialpath,initial),(generalpath,general)]:
    assert all(sha(p)==h for p,h in j['pins'].items());pins[str(path)]=sha(path)
first=read(H/'data/reduced-pairs/result.json');second=read(H/'data/remaining-pairs/result.json')
assert len(first['results'])==5 and {r['id'] for r in first['results']}=={0,1,14,15,16}
assert len(second['results'])==52 and {r['id'] for r in second['results']}==set(general['representatives'])
assert all(r['status']=='INFEASIBLE' and len(r['iterations'])==1 and not r['cycle_cuts'] for j in [first,second] for r in j['results'])
initial_map={i:0 for i in [0,2,4,6,8,10,12,17]};initial_map.update({i:1 for i in [1,3,5,7,9,11,13]});initial_map.update({i:i for i in [14,15,16]})
general_map={i:general['dominated'].get(str(g[0]),g[0]) for g in general['exact_groups'] for i in g}
assert set(general_map)==set(range(len(general['configurations']))) and set(general_map.values())<=set(general['representatives'])
cover=[]
for j,mapping,tag in [(initial,initial_map,'reduced-pairs'),(general,general_map,'remaining-pairs')]:
    for row in j['contexts']:
        ident=row['context'];assert combined[ident]['status']=='UNKNOWN'
        reps=sorted({mapping[k] for k in row['configurations']})
        entry=dict(context=ident,configurations=row['configurations'],representatives=reps,batch=tag)
        cover.append(entry);combined[ident].update(status='REDUCED_PAIR_EXCLUDED',cover=entry)
assert len(cover)==42 and not any(r['status']=='UNKNOWN' for r in combined.values())
portpath=R/'milestones/226-connected-replacement-search/data/ports44-232.json';port=read(portpath)
assert all(r['status']=='INFEASIBLE' for r in port['results'] if r['id'] in [194,195,196,197,198,199,201]);pins[str(portpath)]=sha(portpath)
out=dict(status='COMPLETE_NATIVE_EXCLUSION',round=227,width=44,contexts=301,newly_excluded_contexts=42,initial_configurations=18,other_configurations=230,initial_representatives=5,other_representatives=52,contexts_table=[combined[i] for i in sorted(combined)],new_cover=cover,initial_configuration_map=initial_map,other_configuration_map=general_map,pins=pins,scope='All301 maximal width44 contexts of the fixedseed endpoint24 two-block length-preserving construction withfour bit8crossings. Includes prior native exclusions and prior232port exclusions. No Lean solver contradiction or complete traversal certificate; not a global upper bound.')
save(H/'data/coverage44.json',out)
save(H/'data/search-summary.json',dict(round=227,status='PROGRESS',complete_through=44,width44_contexts=301,width44_unresolved=[],new_context_exclusions=42,reduced_queries=57,reduced_native_infeasible=57,new_q9_record=False,new_global_bound=False,runs=runs,coverage_sha256=sha(H/'data/coverage44.json'),dfs_superseded=True,scope=out['scope']))
print('COMPLETE_NATIVE_WIDTH44_COVER',len(combined),'contexts;',len(cover),'newly excluded')
