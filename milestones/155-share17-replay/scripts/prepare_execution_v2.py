"""Prepare native-resource pilot execution; preserve every original155 file."""
from pathlib import Path
import ast, copy, hashlib, importlib.util, json

H=Path(__file__).resolve().parents[1];R=H.parents[1]
read=lambda p:json.loads(Path(p).read_text(encoding='utf-8-sig'))
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def put(path,content):
    raw=content.encode('utf-8') if isinstance(content,str) else content
    path.parent.mkdir(parents=True,exist_ok=True)
    if path.exists():assert path.read_bytes()==raw,path
    else:path.write_bytes(raw)
def once(text,old,new):
    assert text.count(old)==1,(old,text.count(old));return text.replace(old,new)

oldpath=H/'data/preparation.json';old=read(oldpath)
assert old['status']=='PREPARED_IMMUTABLE_PILOT_EXECUTION_UNCHECKED'
for name,digest in old['execution_scripts_sha256'].items():assert sha(H/name)==digest,name
planpath=H/'data/pilot-source-plan.json';plan=read(planpath)
assert sha(planpath)==old['pilot_plan_sha256']
assert len(plan['module_order'])==34
for row in plan['artifacts']:assert sha(H/row['path'])==row['sha256'],row['path']
assert not any((H/'data').glob('*-audit.json')), 'Inspect accepted receipts before changing runner version'
helper_source=R/'milestones/154-share17-broader-semantics/scripts/native_resources.py'
helper=H/'scripts/native_resources.py';put(helper,helper_source.read_bytes())

renames={'check_replay.py':'check_replay_v2.py','run_replay.py':'run_replay_v2.py',
         'finish_pilot.py':'finish_pilot_v2.py','emit_full.py':'emit_full_v2.py'}
def common(text):
    for oldname,newname in renames.items():text=text.replace(oldname,newname)
    text=text.replace('data/preparation.json','data/preparation-v2.json')
    text=text.replace('data/replay-progress.json','data/replay-progress-v2.json')
    text=text.replace('data/replay-batch.lock','data/replay-batch-v2.lock')
    text=text.replace('data/pilot-completion.json','data/pilot-completion-v2.json')
    text=text.replace('PREPARED_IMMUTABLE_PILOT_EXECUTION_UNCHECKED','PREPARED_NATIVE_RESOURCE_PILOT_EXECUTION_UNCHECKED')
    return text
checker=common((H/'scripts/check_replay.py').read_text(encoding='utf-8'))
checker=once(checker,'import argparse,hashlib,json,os,re,subprocess,time',
    'import argparse,hashlib,json,os,re,subprocess,time\nfrom native_resources import snapshot as resources')
begin=checker.index('def resources():');end=checker.index('pre_gate=resources();',begin)
checker=checker[:begin]+checker[end:]
checker=once(checker,"assert sha(planpath)==prep['pilot_plan_sha256']",
    "assert sha(planpath)==prep['pilot_plan_sha256']\n"
    "helper=H/'scripts/native_resources.py';assert sha(helper)==prep['resource_helper_sha256']")
checker=once(checker,
    "pre_gate=resources();assert pre_gate['free_bytes']>=1.5*1024**3 and len(pre_gate['processes'])==0,pre_gate",
    "pre_gate=resources();assert not pre_gate['errors'] and pre_gate['free_bytes']>=1.5*1024**3 and len(pre_gate['processes'])==0,pre_gate")
checker=once(checker,
    "deps={str(planpath):sha(planpath),str(prep_path):sha(prep_path),str(B/'lean.exe'):sha(B/'lean.exe')}",
    "deps={str(planpath):sha(planpath),str(prep_path):sha(prep_path),str(B/'lean.exe'):sha(B/'lean.exe'),str(helper):sha(helper)}")
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
    "        if sample['free_bytes']<state['minimum_free_bytes'] and stop is None:stop='LOW_FREE_MEMORY'")
assert 'Get-CimInstance' not in checker
put(H/'scripts/check_replay_v2.py',checker)
runner=common((H/'scripts/run_replay.py').read_text(encoding='utf-8'))
runner=runner.replace("'replay-batch-'","'replay-batch-v2-'")
runner=runner.replace("'replay-launch-'","'replay-launch-v2-'")
runner=once(runner,"assert a.limit is None or a.limit>0",
    "assert a.limit is None or a.limit>0\n"
    "assert not (H/'data/replay-batch.lock').exists(), 'Inspect original driver before launching v2'\n"
    "assert sha(H/'scripts/native_resources.py')==prep['resource_helper_sha256']")
put(H/'scripts/run_replay_v2.py',runner)
put(H/'scripts/finish_pilot_v2.py',common((H/'scripts/finish_pilot.py').read_text(encoding='utf-8')))
put(H/'scripts/emit_full_v2.py',common((H/'scripts/emit_full.py').read_text(encoding='utf-8')))
new=copy.deepcopy(old)
new['status']='PREPARED_NATIVE_RESOURCE_PILOT_EXECUTION_UNCHECKED'
new['execution_scripts_sha256']={f'scripts/{name}':sha(H/'scripts'/name) for name in renames.values()}
new['preparation_script_sha256']=sha(Path(__file__))
new['resource_helper_sha256']=sha(helper)
new['resource_helper_origin']=helper_source.relative_to(R).as_posix()
new['input_pins'][helper.relative_to(R).as_posix()]=sha(helper)
new['input_pins'][helper_source.relative_to(R).as_posix()]=sha(helper_source)
new['original_package_pins']={p.relative_to(R).as_posix():sha(p) for p in
    [oldpath,planpath,H/'scripts/prepare.py',H/'scripts/verify_preparation.py']+[H/'scripts'/name for name in renames]}
new['progress_file']='data/replay-progress-v2.json'
new['lock_file']='data/replay-batch-v2.lock'
new['pilot_completion_file']='data/pilot-completion-v2.json'
new['scope']='Native-resource execution sources only, with unchanged34 source modules and source plan. No compiler or solver invocation. Full generation remains gated by complete pilot-v2 evidence.'
put(H/'data/preparation-v2.json',json.dumps(new,indent=2)+'\n')
for name in [*renames.values(),'native_resources.py','prepare_execution_v2.py']:
    ast.parse((H/'scripts'/name).read_text(encoding='utf-8'),filename=name)
for path,digest in new['original_package_pins'].items():assert sha(R/path)==digest,path
print(json.dumps(dict(status=new['status'],modules=34,Lean_started=False,
    preparation_sha256=sha(H/'data/preparation-v2.json'),helper_sha256=sha(helper),
    pilot_source_plan_sha256=sha(planpath),original_files_unchanged=True)))
