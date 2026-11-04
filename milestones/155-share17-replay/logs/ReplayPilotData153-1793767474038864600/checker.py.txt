"""Check one minimal-import module with exact receipts and bounded resources."""
from pathlib import Path
import argparse,hashlib,json,os,re,subprocess,time
from native_resources import snapshot as resources
H=Path(__file__).resolve().parents[1];R=H.parents[1]
P=R/'milestones/154-share17-broader-semantics';Q=R/'milestones/147-countfree-clause-semantics'
B=Path(os.environ.get('SNAKE_LEAN_BIN', 'D:/Codex/2026-10-01/it-should-have-a-property-of/work/lean-research/lean-4.19.0-windows/bin')).resolve()
read=lambda p:json.loads(Path(p).read_text(encoding='utf-8-sig'))
def sha(p):
    d=hashlib.sha256()
    with Path(p).open('rb') as f:
        for b in iter(lambda:f.read(1048576),b''):d.update(b)
    return d.hexdigest()
ap=argparse.ArgumentParser();ap.add_argument('module');ap.add_argument('--timeout',type=int,default=180)
a=ap.parse_args();assert re.fullmatch(r'[A-Za-z][A-Za-z0-9._]*',a.module)
src=H/'lean'/(a.module.replace('.','/')+'.lean');source=src.read_text(encoding='utf-8')
assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b',source)
planpath=H/'data/pilot-source-plan.json';plan=read(planpath)
expected={x['module']:x['sha256'] for x in plan['artifacts']}
assert a.module in expected and sha(src)==expected[a.module]
prep_path=H/'data/preparation-v2.json';prep=read(prep_path)
assert prep['status']=='PREPARED_NATIVE_RESOURCE_PILOT_EXECUTION_UNCHECKED'
assert sha(planpath)==prep['pilot_plan_sha256']
helper=H/'scripts/native_resources.py';assert sha(helper)==prep['resource_helper_sha256']
assert sha(Path(__file__))==prep['execution_scripts_sha256']['scripts/check_replay_v2.py']
for p,d in prep['original_source_pins'].items():assert sha(R/p)==d,p
build=H/'build';build.mkdir(exist_ok=True)
stable=build/(a.module.replace('.','/')+'.olean');assert not stable.exists(),stable
env=os.environ.copy();env['PATH']=str(B)+';'+env['PATH'];env['LEAN_PATH']=';'.join(map(str,[build,P/'build',Q/'build']))
pre_gate=resources();assert not pre_gate['errors'] and pre_gate['free_bytes']>=1.5*1024**3 and len(pre_gate['processes'])==0,pre_gate
start=time.monotonic();stamp=str(time.time_ns())
folder=H/'logs'/(a.module+'-'+stamp);folder.mkdir(parents=True)
log=folder/'compiler.log';rec=folder/'record.json'
(folder/'source.lean.txt').write_bytes(src.read_bytes());(folder/'checker.py.txt').write_bytes(Path(__file__).read_bytes())
deps={str(planpath):sha(planpath),str(prep_path):sha(prep_path),str(B/'lean.exe'):sha(B/'lean.exe'),str(helper):sha(helper)}
for p,d in prep['original_source_pins'].items():deps[str(R/p)]=d
version=subprocess.check_output([str(B/'lean.exe'),'--version'],env=env,cwd=R,text=True).strip()
assert version.startswith('Lean (version 4.19.0'),version
direct=subprocess.check_output([str(B/'lean.exe'),'--deps',str(src)],env=env,cwd=R,text=True).splitlines()
for name in re.findall(r'^import ([\w.]+)$',source,re.M):
    if name=='Std':continue
    rp=H/'data'/(name+'-audit.json')
    if not rp.exists():rp=P/'data'/(name+'-audit.json')
    if not rp.exists():rp=Q/'data'/(name+'-audit.json')
    q=read(rp)
    assert q['status']=='PASS' and q['exit_code']==0 and q['stop_reason'] is None
    assert sha(q['source'])==q['source_sha256'] and sha(q['object'])==q['olean_sha256']
    assert sha(q['log'])==q['log_sha256']
    qfolder=Path(q['log']).parent
    assert sha(qfolder/'source.lean.txt')==q['source_sha256']
    assert sha(qfolder/'checker.py.txt')==q['checker_sha256']
    assert all(set(x['axioms'])<={'propext','Classical.choice','Quot.sound'} for x in q['axioms'])
    if name=='LocalWindowCnf.ShareWindow153':
        assert rp==P/'data/LocalWindowCnf.ShareWindow153-audit.json'
        assert q['source_sha256']==prep['shared_cnf_source_sha256']
        assert Path(q['object']).resolve()==(P/'build/LocalWindowCnf/ShareWindow153.olean').resolve()
    assert Path(q['object']).resolve() in {Path(x).resolve() for x in direct}
    deps[q['log']]=q['log_sha256']
    deps[str(qfolder/'source.lean.txt')]=q['source_sha256']
    deps[str(qfolder/'checker.py.txt')]=q['checker_sha256']
    deps[str(rp)]=sha(rp);deps[q['source']]=q['source_sha256'];deps[q['object']]=q['olean_sha256']
    for p,d in q['dependencies'].items():
        if p in deps:assert deps[p]==d,p
        else:
            assert sha(p)==d,p;deps[p]=d
for value in direct:
    p=Path(value).resolve();assert p.is_file(),p
    assert any(p.is_relative_to(root.resolve()) for root in [build,P/'build',Q/'build',B.parent/'lib/lean']),p
    deps[str(p)]=sha(p)
gate=resources();assert not gate['errors'] and gate['free_bytes']>=1.5*1024**3 and len(gate['processes'])==0,gate
generic=a.module in ['LratCheck153Replay','LratFast153Replay','InputTree153Replay','ReplayTools153']
obj=stable.with_name(stable.stem+'.'+stamp+'.olean');obj.parent.mkdir(parents=True,exist_ok=True)
state=dict(status='RUNNING',pid=os.getpid(),module=a.module,source=str(src),source_sha256=sha(src),
    checker_sha256=sha(__file__),dependencies=deps,toolchain_version=version,direct_dependencies=direct,
    stdlib_scope='The standard Lean4.19 library is trusted; compiler and direct standard-library objects are pinned. The34 pilot modules are freshly checked. The exact shared CNF from154 and generic local models from147 are reused with pinned source/object/log/dependency receipts. Each dependency is hashed once in preflight and again after compilation.',
    resource_gate=gate,resource_samples=[],timeout_seconds=a.timeout,memory_limit_bytes=3*1024**3,
    minimum_free_bytes=768*1024**2,compiler_threads=1 if generic else 2,
    compiler_stack_kb=8192 if generic else 65536,
    preflight_seconds=time.monotonic()-start,log=str(log),paths=[str(build),str(P/'build'),str(Q/'build')])
def save():rec.write_text(json.dumps(state,indent=2)+'\n',encoding='utf-8',newline='\n')
cmd=[str(B/'lean.exe'),'-j',str(state['compiler_threads']),'-s',str(state['compiler_stack_kb'])]
cmd+=['-R',str(H/'lean'),'-o',str(obj),str(src)]
state['command']=cmd;save();compile_start=time.monotonic();stop=None
with log.open('w',encoding='utf-8') as out:
    child=subprocess.Popen(cmd,env=env,cwd=R,stdout=out,stderr=subprocess.STDOUT)
    state['compiler_pid']=child.pid;save()
    while child.poll() is None:
        if time.monotonic()-compile_start>a.timeout:stop='TIMEOUT'
        try:
            sample=resources()
        except Exception as error:
            sample=dict(free_bytes=0,processes=[],errors=[dict(exception=repr(error))])
        sample['seconds']=time.monotonic()-compile_start
        if sample['errors']:stop='RESOURCE_QUERY_FAILED'
        own=[p for p in sample['processes'] if int(p['ProcessId'])==child.pid]
        sample['owned_lean_processes']=own;state['resource_samples'].append(sample);save()
        if any(int(p['PrivatePageCount'])>state['memory_limit_bytes'] for p in own):stop='MEMORY_LIMIT'
        if sample['free_bytes']<state['minimum_free_bytes'] and stop is None:stop='LOW_FREE_MEMORY'
        if any(int(p['ProcessId'])!=child.pid for p in sample['processes']):stop='OTHER_LEAN_PROCESS'
        if stop:
            subprocess.run(['taskkill','/PID',str(child.pid),'/T','/F'],stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL);break
        time.sleep(1)
    code=child.wait(timeout=30)
compiler_seconds=time.monotonic()-compile_start;post_start=time.monotonic()
output=log.read_text(encoding='utf-8')
reports=[dict(theorem=n,axioms=re.findall(r'[A-Za-z][\w.]*',x)) for n,x in re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",output,re.S)]
reports += [dict(theorem=n,axioms=[]) for n in re.findall(r"'([^']+)' does not depend on any axioms",output)]
ok=code==0 and stop is None and 'error:' not in output and 'sorryAx' not in output
ok=ok and len(reports)==source.count('#print axioms') and all(set(x['axioms'])<={'propext','Classical.choice','Quot.sound'} for x in reports)
ok=ok and sha(src)==state['source_sha256'] and sha(__file__)==state['checker_sha256'] and all(sha(p)==d for p,d in deps.items())
state.update(status='PASS' if ok else 'FAILED',exit_code=code,stop_reason=stop,
    compiler_wall_seconds=compiler_seconds,postflight_seconds=time.monotonic()-post_start,
    seconds=time.monotonic()-start,axioms=reports,log_sha256=sha(log))
if ok:
    os.replace(obj,stable);state.update(object=str(stable),olean_sha256=sha(stable))
save()
if ok:(H/'data'/(a.module+'-audit.json')).write_bytes(rec.read_bytes())
print(json.dumps({k:state[k] for k in ['status','preflight_seconds','compiler_wall_seconds','postflight_seconds','seconds','stop_reason','axioms']}),flush=True)
raise SystemExit(0 if ok else 1)
