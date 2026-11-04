"""Verify source copies and pending-result rejection without invoking Lean."""
from pathlib import Path
import ast, hashlib, json, re, subprocess, sys

H=Path(__file__).resolve().parents[1];R=H.parents[1]
read=lambda p:json.loads(Path(p).read_text(encoding='utf-8-sig'))
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
prep=read(H/'data/preparation.json');plan=read(H/'data/pilot-source-plan.json')
assert prep['status']=='PREPARED_IMMUTABLE_PILOT_EXECUTION_UNCHECKED'
assert sha(H/'data/pilot-source-plan.json')==prep['pilot_plan_sha256']
assert sha(H/'scripts/prepare.py')==prep['preparation_script_sha256']
for name,digest in prep['execution_scripts_sha256'].items():
    assert sha(H/name)==digest,name
    ast.parse((H/name).read_text(encoding='utf-8'),filename=name)
for p,digest in prep['original_source_pins'].items():assert sha(R/p)==digest,p
for p,digest in prep['input_pins'].items():assert sha(R/p)==digest,p
order={module:i for i,module in enumerate(plan['module_order'])}
external=set();expected_reports=0
assert len(order)==len(plan['artifacts'])==34
for row in plan['artifacts']:
    p=H/row['path'];assert sha(p)==row['sha256'] and p.stat().st_size==row['bytes']
    text=p.read_text(encoding='utf-8');expected_reports+=text.count('#print axioms')
    assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b',text)
    for dependency in re.findall(r'^import ([\w.]+)$',text,re.M):
        if dependency in order:assert order[dependency]<order[row['module']],(row['module'],dependency)
        else:external.add(dependency)
assert external=={'LocalWindowModel','LocalWindowCnf.ShareWindow153'},external
assert not (H/'data/replay-progress.json').exists()
assert not (H/'data/pilot-completion.json').exists()
assert not (H/'data/full-source-plan.json').exists()
before={p.relative_to(H).as_posix():sha(p) for p in (H/'lean').rglob('*.lean')}
tests=[]
for name,args,code in [('finish_pilot.py',['--verify-only'],2),('emit_full.py',['--full','--max-source-mib','256'],1)]:
    result=subprocess.run([sys.executable,'-B','-X','utf8',str(H/'scripts'/name),*args],
        cwd=R,capture_output=True,text=True,timeout=30)
    assert result.returncode==code,(name,result.returncode,result.stdout,result.stderr)
    assert 'WAITING_FOR_PILOT_CHECKS' in result.stdout
    tests.append(dict(script=name,arguments=args,expected_exit_code=code,exit_code=result.returncode,
        stdout=result.stdout,stderr=result.stderr))
assert before=={p.relative_to(H).as_posix():sha(p) for p in (H/'lean').rglob('*.lean')}
assert not (H/'data/pilot-completion.json').exists() and not (H/'data/full-source-plan.json').exists()
assert not any((H/'lean').rglob('*.olean'))
out=dict(status='PASS_SOURCE_AND_PENDING_GUARDS_ONLY',copied_modules=34,copied_source_bytes=plan['source_bytes'],
    expected_axiom_reports=expected_reports,external_imports=sorted(external),Lean_started=False,
    full_sources_generated=False,finished_pilot_claim_created=False,pending_guard_tests=tests,
    sources_unchanged=True,preparation_sha256=sha(H/'data/preparation.json'),
    source_plan_sha256=sha(H/'data/pilot-source-plan.json'),verifier_sha256=sha(Path(__file__)),
    scope='Source copies, import order, Python syntax, and refusal to accept/generate beyond a missing pilot. No Lean theorem has been checked by this test.')
target=H/'data/preparation-check.json';assert not target.exists()
target.write_bytes((json.dumps(out,indent=2)+'\n').encode('utf-8'))
print(json.dumps({k:v for k,v in out.items() if k!='pending_guard_tests'}))
