"""Prepare the existing bounded checker for the shared CNF and broader semantics."""
from pathlib import Path
import hashlib,json
H=Path(__file__).resolve().parents[1];R=H.parents[1]
T=R/'milestones/150-actual-pair-share'
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
source=read(H/'data/source-plan.json');old=read(T/'data/semantic-plan.json')
assert sha(H/'data/source-plan.json')=='9074e35df90bb1589133b3d0cf8576510efb279118b4d6f2fb1f0ad0e16246ff'
shared=R/'milestones/153-pair-conditioned-share17/lean/LocalWindowCnf/ShareWindow153.lean'
assert sha(shared)==source['shared_cnf_source_sha256']
artifacts=[dict(module=source['shared_cnf_module'],
    path='../153-pair-conditioned-share17/lean/LocalWindowCnf/ShareWindow153.lean',
    bytes=shared.stat().st_size,sha256=sha(shared))]+source['artifacts']
for row in artifacts:assert sha(H/row['path'])==row['sha256'],row['path']
plan=dict(status='PREPARED_BROADER_CORE_SEMANTICS_AND_CONDITIONAL_TRANSFER',
    module_order=[x['module'] for x in artifacts],artifacts=artifacts,
    framework_modules=['CriticalShareAdapter154'],
    source_plan_sha256=sha(H/'data/source-plan.json'),source_files_sha256=source['source_files_sha256'],
    **{k:old[k] for k in ['inherited_modules','external_library_search_paths','external_pins']},
    scope='One shared153 CNF, broader154 interpretation and actual-snake implication. Unsat remains a premise until the separate single153 replay is complete.')
path=H/'data/semantic-plan.json';assert not path.exists()
path.write_text(json.dumps(plan,indent=2)+'\n',encoding='utf-8')
checker=(T/'scripts/check_module.py').read_text(encoding='utf-8')
checker=checker.replace('The new150 clauses and conditional transfer are freshly checked; the core contradiction remains separate.',
    'The shared153 core and broader154 clause interpretation and conditional transfer are freshly checked; the single153 core contradiction remains separate.')
driver=(T/'scripts/run_semantics.py').read_text(encoding='utf-8')
driver=driver.replace('PREPARED_COUNTFREE_CORE_SEMANTICS_AND_CONDITIONAL_TRANSFER',
    'PREPARED_BROADER_CORE_SEMANTICS_AND_CONDITIONAL_TRANSFER')
driver=driver.replace("lock=H/'data/semantic-batch.lock'", "(H/'logs').mkdir(exist_ok=True)\nlock=H/'data/semantic-batch.lock'")
for name,text in [('check_module.py',checker),('run_semantics.py',driver)]:
    path=H/'scripts'/name;assert not path.exists();path.write_text(text,encoding='utf-8',newline='\n')
print(json.dumps(dict(status='PREPARED_98_MODULE_EXECUTION_PLAN',modules=len(artifacts),
    Lean_invoked=False,plan_sha256=sha(H/'data/semantic-plan.json'))))
