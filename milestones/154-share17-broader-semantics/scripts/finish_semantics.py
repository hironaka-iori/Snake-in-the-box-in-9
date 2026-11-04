"""Audit every broader interpretation receipt; retain the explicit Unsat premise."""
from pathlib import Path
import hashlib,json,re
H=Path(__file__).resolve().parents[1];R=H.parents[1]
read=lambda p:json.loads(Path(p).read_text(encoding='utf-8-sig'))
cache={}
def sha(p):
    p=Path(p);key=(str(p.resolve()),p.stat().st_size,p.stat().st_mtime_ns)
    if key not in cache:cache[key]=hashlib.sha256(p.read_bytes()).hexdigest()
    return cache[key]
plan=read(H/'data/semantic-plan.json');progress=read(H/'data/semantic-progress.json')
assert progress['status']=='PASS_COMPLETE_CORE_SEMANTICS_AND_CONDITIONAL_TRANSFER'
assert len(progress['checked_modules'])==len(plan['module_order'])==98 and progress['active'] is None
assert [x['module'] for x in progress['checked_modules']]==plan['module_order']
assert not (H/'data/semantic-batch.lock').exists()
assert sha(H/'data/semantic-plan.json')==progress['plan_sha256']
assert sha(H/'scripts/check_module.py')==progress['checker_sha256']
assert sha(H/'scripts/run_semantics.py')==progress['driver_sha256']
artifacts={x['module']:x for x in plan['artifacts']};rows=[]
for item in progress['checked_modules']:
    m=item['module'];path=H/'data'/(m+'-audit.json');q=read(path);source=H/artifacts[m]['path']
    assert sha(path)==item['receipt_sha256']
    assert q['status']=='PASS' and q['exit_code']==0 and q['stop_reason'] is None,m
    assert sha(source)==artifacts[m]['sha256']==q['source_sha256']
    assert sha(q['object'])==q['olean_sha256'] and sha(q['log'])==q['log_sha256']
    folder=Path(q['log']).parent
    assert sha(folder/'source.lean.txt')==q['source_sha256']
    assert sha(folder/'checker.py.txt')==q['checker_sha256']==progress['checker_sha256']
    for p,d in q['dependencies'].items():assert sha(p)==d,p
    text=source.read_text(encoding='utf-8')
    assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b',text)
    assert len(q['axioms'])==text.count('#print axioms')
    assert all(set(x['axioms'])<={'propext','Classical.choice','Quot.sound'} for x in q['axioms'])
    rows.append(dict(module=m,receipt=path.relative_to(R).as_posix(),sha256=sha(path),axioms=q['axioms']))
adapter=(H/'lean/CriticalShareAdapter154.lean').read_text(encoding='utf-8')
assert '(hunsat : Unsat ShareWindow153.cnf)' in adapter
assert '[(4,4),(0,4),(4,4),(0,5),(3,3)]' in adapter
reports=sum(len(x['axioms']) for x in rows)
record=dict(status='PASS_BROADER_CORE_SEMANTICS_AND_CONDITIONAL_ACTUAL_SNAKE_SHARE17',
    checked_modules=98,axiom_reports=reports,shared_core_clauses=11869,counter_count=9,
    directions=[0,1,2,0,3,2],bounds=[[4,4],[0,4],[4,4],[0,5],[3,3]],
    reverse_bounds=[[3,3],[0,5],[4,4],[0,4],[4,4]],
    share_resolution=12,share_lower_bound=17,canonical_and_reverse_cases_checked=True,
    core_unsat_is_explicit_premise=True,complete_contradiction_checked=False,
    unconditional_actual_snake_share17_complete=False,new_global_upper_bound=False,
    receipts=rows,plan_sha256=sha(H/'data/semantic-plan.json'),
    source_plan_sha256=sha(H/'data/source-plan.json'),progress_sha256=sha(H/'data/semantic-progress.json'),
    trusted_scope='Lean4.19 and external mathematics libraries; pinned147 generic framework and148 coordinate/reversal helpers, including a historical data object.',
    remaining='Check the single153 initial-tree pilot and complete contradiction, then compose it with the checked broader actual-snake implication.')
target=H/'data/semantics-completion.json';assert not target.exists()
target.write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:v for k,v in record.items() if k!='receipts'}))
