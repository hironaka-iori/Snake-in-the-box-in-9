"""Check native-resource pilot sources and pending guards without Lean."""
from pathlib import Path
import ast, hashlib, importlib.util, json, re, subprocess, sys

H=Path(__file__).resolve().parents[1];R=H.parents[1]
read=lambda p:json.loads(Path(p).read_text(encoding='utf-8-sig'))
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
prep=read(H/'data/preparation-v2.json');plan=read(H/'data/pilot-source-plan.json')
assert prep['status']=='PREPARED_NATIVE_RESOURCE_PILOT_EXECUTION_UNCHECKED'
assert sha(H/'data/pilot-source-plan.json')==prep['pilot_plan_sha256']
assert sha(H/'scripts/prepare_execution_v2.py')==prep['preparation_script_sha256']
for name,digest in prep['execution_scripts_sha256'].items():
    assert sha(H/name)==digest,name
    ast.parse((H/name).read_text(encoding='utf-8'),filename=name)
for mapping in ['original_source_pins','input_pins','original_package_pins']:
    for p,digest in prep[mapping].items():assert sha(R/p)==digest,p
helper=H/'scripts/native_resources.py';assert sha(helper)==prep['resource_helper_sha256']
assert helper.read_bytes()==(R/prep['resource_helper_origin']).read_bytes()
assert len(plan['module_order'])==len(plan['artifacts'])==34
for row in plan['artifacts']:
    source=H/row['path'];assert sha(source)==row['sha256'] and source.stat().st_size==row['bytes']
assert 'Get-CimInstance' not in (H/'scripts/check_replay_v2.py').read_text(encoding='utf-8')
assert not (H/'data/replay-progress-v2.json').exists()
assert not (H/'data/pilot-completion-v2.json').exists()
assert not (H/'data/full-source-plan.json').exists()
before={p.relative_to(H).as_posix():sha(p) for p in (H/'lean').rglob('*.lean')}
tests=[]
for name,args,code in [('finish_pilot_v2.py',['--verify-only'],2),('emit_full_v2.py',['--full','--max-source-mib','256'],1)]:
    result=subprocess.run([sys.executable,'-B','-X','utf8',str(H/'scripts'/name),*args],
        cwd=R,capture_output=True,text=True,timeout=30)
    assert result.returncode==code,(name,result.returncode,result.stdout,result.stderr)
    assert 'WAITING_FOR_PILOT_CHECKS' in result.stdout
    tests.append(dict(script=name,arguments=args,expected_exit_code=code,exit_code=result.returncode,
        stdout=result.stdout,stderr=result.stderr))
assert before=={p.relative_to(H).as_posix():sha(p) for p in (H/'lean').rglob('*.lean')}
assert not (H/'data/pilot-completion-v2.json').exists() and not (H/'data/full-source-plan.json').exists()
spec=importlib.util.spec_from_file_location('resource_check155v2',helper)
native=importlib.util.module_from_spec(spec);spec.loader.exec_module(native)
snapshot=native.snapshot();assert not snapshot['errors'],snapshot
out=dict(status='PASS_NATIVE_RESOURCE_SOURCE_AND_PENDING_GUARDS_ONLY',copied_modules=34,
    copied_source_bytes=plan['source_bytes'],Lean_started=False,solver_started=False,
    full_sources_generated=False,finished_pilot_claim_created=False,pending_guard_tests=tests,
    native_snapshot=snapshot,source_plan_unchanged=True,original155_files_unchanged=True,
    preparation_sha256=sha(H/'data/preparation-v2.json'),
    source_plan_sha256=sha(H/'data/pilot-source-plan.json'),helper_sha256=sha(helper),
    verifier_sha256=sha(Path(__file__)),
    scope='V2 execution-source identities, syntax, native snapshot, and refusal of incomplete pilot acceptance/full generation. No Lean theorem was checked. A concurrent154 Lean process may appear in the read-only snapshot.')
target=H/'data/preparation-v2-check.json';assert not target.exists()
target.write_bytes((json.dumps(out,indent=2)+'\n').encode('utf-8'))
print(json.dumps({k:v for k,v in out.items() if k!='pending_guard_tests'}))
