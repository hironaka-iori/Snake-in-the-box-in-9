"""Prepare native-resource semantic recovery without invoking any compiler."""
from pathlib import Path
import ast, copy, hashlib, importlib.util, json, subprocess, time

H=Path(__file__).resolve().parents[1];R=H.parents[1]
read=lambda p:json.loads(Path(p).read_text(encoding='utf-8-sig'))
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def put(path, content):
    raw=content.encode('utf-8') if isinstance(content,str) else content
    path.parent.mkdir(parents=True,exist_ok=True)
    if path.exists():assert path.read_bytes()==raw,path
    else:path.write_bytes(raw)
def once(text, old, new):
    assert text.count(old)==1,(old,text.count(old));return text.replace(old,new)

oldplan_path=H/'data/semantic-plan.json';oldplan=read(oldplan_path)
oldprogress_path=H/'data/semantic-progress.json';oldprogress=read(oldprogress_path)
assert oldprogress['status']=='STOPPED_ON_FAILED_OR_INCOMPLETE_MODULE' and oldprogress['active'] is None
assert len(oldprogress['checked_modules'])==1
assert oldprogress['checked_modules'][0]['module']=='LocalWindowCnf.ShareWindow153'
put(H/'audit/semantic-progress-before-v2.json',oldprogress_path.read_bytes())
prior=R/'milestones/150-actual-pair-share/data/semantic-plan.json'
prior_plan=read(prior)
assert 'Share150.Data' in prior_plan['framework_modules']
assert all(m in prior_plan['framework_modules'] for m in prior_plan['module_order'])
shared_path=H/'data/LocalWindowCnf.ShareWindow153-audit.json';shared=read(shared_path)
assert shared['status']=='PASS' and shared['exit_code']==0 and shared['stop_reason'] is None
assert sha(shared_path)==oldprogress['checked_modules'][0]['receipt_sha256']
assert shared['checker_sha256']==sha(H/'scripts/check_module.py')
for p,digest in shared['dependencies'].items():assert sha(p)==digest,p
assert sha(shared['source'])==shared['source_sha256'] and sha(shared['object'])==shared['olean_sha256']
assert sha(shared['log'])==shared['log_sha256']
for row in oldplan['artifacts']:assert sha(H/row['path'])==row['sha256'],row['path']
plan=copy.deepcopy(oldplan)
plan['framework_modules']=list(plan['module_order'])
assert len(plan['module_order'])==98
plan['recovery_v2']=dict(original_plan_sha256=sha(oldplan_path),
    original_progress_sha256=sha(oldprogress_path),
    original_checker_sha256=sha(H/'scripts/check_module.py'),
    original_runner_sha256=sha(H/'scripts/run_semantics.py'),
    classification_reference=prior.relative_to(R).as_posix(),classification_reference_sha256=sha(prior),
    compiler_policy='Every one of98 modules uses one thread and8192KiB stack, matching150 framework classification.',
    resource_helper_sha256=sha(H/'scripts/native_resources.py'),
    reused_receipts={'LocalWindowCnf.ShareWindow153':dict(receipt_sha256=sha(shared_path),checker_sha256=shared['checker_sha256'])},
    source_artifacts_unchanged=True)
put(H/'data/semantic-plan-v2.json',json.dumps(plan,indent=2)+'\n')

checker=(H/'scripts/check_module.py').read_text(encoding='utf-8')
checker=checker.replace("'data/semantic-plan.json'","'data/semantic-plan-v2.json'")
checker=once(checker,'import argparse,hashlib,json,os,re,subprocess,time',
    'import argparse,hashlib,json,os,re,subprocess,time\nfrom native_resources import snapshot as resources')
begin=checker.index('def resources():');end=checker.index('gate=resources();',begin)
checker=checker[:begin]+checker[end:]
checker=once(checker,'assert a.module in expected and sha(src)==expected[a.module]',
    "assert a.module in expected and sha(src)==expected[a.module]\n"
    "helper=H/'scripts/native_resources.py'\n"
    "assert sha(helper)==plan['recovery_v2']['resource_helper_sha256']\n"
    "pre_gate=resources();assert not pre_gate['errors'] and pre_gate['free_bytes']>=1.5*1024**3 and not pre_gate['processes'],pre_gate")
checker=once(checker,"deps={str(planpath):sha(planpath),str(B/'lean.exe'):sha(B/'lean.exe')}",
    "deps={str(planpath):sha(planpath),str(B/'lean.exe'):sha(B/'lean.exe'),str(helper):sha(helper)}")
checker=once(checker,
    "gate=resources();assert gate['free_bytes']>=1.5*1024**3 and len(gate['processes'])==0,gate",
    "gate=resources();assert not gate['errors'] and gate['free_bytes']>=1.5*1024**3 and len(gate['processes'])==0,gate")
checker=once(checker,"        sample=resources();sample['seconds']=time.monotonic()-compile_start",
    "        try:\n"
    "            sample=resources()\n"
    "        except Exception as error:\n"
    "            sample=dict(free_bytes=0,processes=[],errors=[dict(exception=repr(error))])\n"
    "        sample['seconds']=time.monotonic()-compile_start\n"
    "        if sample['errors']:stop='RESOURCE_QUERY_FAILED'")
checker=once(checker,"        if sample['free_bytes']<state['minimum_free_bytes']:stop='LOW_FREE_MEMORY'",
    "        if sample['free_bytes']<state['minimum_free_bytes'] and stop is None:stop='LOW_FREE_MEMORY'\n"
    "        if any(int(p['ProcessId'])!=child.pid for p in sample['processes']):stop='OTHER_LEAN_PROCESS'")
assert 'Get-CimInstance' not in checker
put(H/'scripts/check_module_v2.py',checker)

runner=(H/'scripts/run_semantics.py').read_text(encoding='utf-8')
runner=runner.replace("'data/semantic-plan.json'","'data/semantic-plan-v2.json'")
runner=runner.replace("'scripts/check_module.py'","'scripts/check_module_v2.py'")
runner=runner.replace("'data/semantic-batch.lock'","'data/semantic-batch-v2.lock'")
runner=runner.replace("'semantic-batch-'","'semantic-batch-v2-'")
runner=runner.replace("'data/semantic-progress.json'","'data/semantic-progress-v2.json'")
runner=once(runner,"assert a.limit is None or a.limit>0",
    "assert a.limit is None or a.limit>0\n"
    "assert not (H/'data/semantic-batch.lock').exists(), 'Inspect original driver before launching v2'\n"
    "assert sha(H/'data/semantic-plan.json')==plan['recovery_v2']['original_plan_sha256']\n"
    "assert sha(H/'scripts/native_resources.py')==plan['recovery_v2']['resource_helper_sha256']")
runner=once(runner,"    assert all(set(x['axioms'])<={'propext','Classical.choice','Quot.sound'} for x in j['axioms'])",
    "    assert len(j['axioms'])==Path(j['source']).read_text(encoding='utf-8').count('#print axioms')\n"
    "    prior=plan['recovery_v2']['reused_receipts'].get(m)\n"
    "    if prior is not None:\n"
    "        assert sha(rp)==prior['receipt_sha256'] and j['checker_sha256']==prior['checker_sha256']\n"
    "    else:\n"
    "        assert j['checker_sha256']==sha(H/'scripts/check_module_v2.py')\n"
    "    assert all(set(x['axioms'])<={'propext','Classical.choice','Quot.sound'} for x in j['axioms'])")
put(H/'scripts/run_semantics_v2.py',runner)
for name in ['native_resources.py','prepare_checks_v2.py','check_module_v2.py','run_semantics_v2.py']:
    ast.parse((H/'scripts'/name).read_text(encoding='utf-8'),filename=name)
assert plan['artifacts']==oldplan['artifacts'] and plan['module_order']==oldplan['module_order']
spec=importlib.util.spec_from_file_location('native_resource_probe154',H/'scripts/native_resources.py')
native=importlib.util.module_from_spec(spec);spec.loader.exec_module(native)
before=native.snapshot();assert not before['errors'],before
command="$o=Get-CimInstance Win32_OperatingSystem;$p=@(Get-CimInstance Win32_Process -Filter \"Name='lean.exe'\"|Select-Object ProcessId,ParentProcessId,PrivatePageCount);@{free_bytes=[long]$o.FreePhysicalMemory*1024;processes=$p}|ConvertTo-Json -Depth 3 -Compress"
started=time.monotonic()
try:
    observed=subprocess.run(['powershell','-NoProfile','-Command',command],capture_output=True,text=True,timeout=12)
    comparison=dict(status='RETURNED' if observed.returncode==0 else 'FAILED',seconds=time.monotonic()-started,
                    exit_code=observed.returncode,stderr=observed.stderr)
    if observed.returncode==0:comparison['snapshot']=json.loads(observed.stdout)
except subprocess.TimeoutExpired:
    comparison=dict(status='TIMEOUT_ONE_OBSERVATION',seconds=time.monotonic()-started,timeout_seconds=12)
after=native.snapshot();assert not after['errors'],after
if comparison['status']=='RETURNED':
    cim=comparison['snapshot'];low=min(before['free_bytes'],after['free_bytes']);high=max(before['free_bytes'],after['free_bytes'])
    comparison['free_bytes_within_native_bracket_plus128MiB']=low-128*1024**2<=cim['free_bytes']<=high+128*1024**2
    a={x['ProcessId']:x for x in before['processes']};b={x['ProcessId']:x for x in after['processes']}
    c={x['ProcessId']:x for x in cim['processes']}
    comparison['stable_pid_sets_equal']=set(a)==set(b)==set(c)
    comparison['stable_process_memory']=[dict(pid=pid,native_before=a[pid]['PrivatePageCount'],
        cim=c[pid]['PrivatePageCount'],native_after=b[pid]['PrivatePageCount']) for pid in sorted(set(a)&set(b)&set(c))]
record=dict(status='PREPARED_NATIVE_RESOURCE_RECOVERY_UNCHECKED',Lean_started=False,
    source_artifacts_identical=True,modules=98,compiler_threads=1,compiler_stack_kb=8192,
    reused_accepted_modules=['LocalWindowCnf.ShareWindow153'],original_files_unchanged=True,
    native_before=before,native_after=after,one_cim_observation=comparison,
    preflight_gate_current=after['free_bytes']>=1.5*1024**3 and not after['processes'],
    source_files_sha256={p.relative_to(R).as_posix():sha(p) for p in [Path(__file__),
        H/'scripts/native_resources.py',H/'scripts/check_module_v2.py',H/'scripts/run_semantics_v2.py',
        H/'data/semantic-plan-v2.json',oldplan_path,oldprogress_path,shared_path,
        H/'scripts/check_module.py',H/'scripts/run_semantics.py',prior]},
    scope='New recovery sources only. Native snapshots and one bounded CIM observation were taken. No compiler or proof check was launched; existing accepted core receipt and all old plans/checkers remain unchanged.')
put(H/'audit/native-resource-recovery-v2.json',json.dumps(record,indent=2)+'\n')
print(json.dumps({k:v for k,v in record.items() if k!='source_files_sha256'}))
