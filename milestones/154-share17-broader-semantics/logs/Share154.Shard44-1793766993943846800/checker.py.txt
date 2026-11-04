"""Check one minimal-import module with exact receipts and bounded resources."""
from pathlib import Path
import argparse,hashlib,json,os,re,subprocess,time
from native_resources import snapshot as resources
H=Path(__file__).resolve().parents[1];R=H.parents[1];Q=R/'milestones/147-countfree-clause-semantics'
B=Path('D:/Codex/2026-10-01/it-should-have-a-property-of/work/lean-research/lean-4.19.0-windows/bin')
read=lambda p:json.loads(Path(p).read_text(encoding='utf-8-sig'))
def sha(p):
    d=hashlib.sha256()
    with Path(p).open('rb') as f:
        for b in iter(lambda:f.read(1048576),b''):d.update(b)
    return d.hexdigest()
ap=argparse.ArgumentParser();ap.add_argument('module');ap.add_argument('--timeout',type=int,default=180)
a=ap.parse_args();assert re.fullmatch(r'[A-Za-z][A-Za-z0-9.]*',a.module)
source_plan=read(H/'data/semantic-plan-v2.json')
src=H/next(x['path'] for x in source_plan['artifacts'] if x['module']==a.module);source=src.read_text(encoding='utf-8')
assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b',source.replace("/- A snake's length is its number of edges. No optimality axiom is declared. -/",''))
planpath=H/'data/semantic-plan-v2.json';plan=read(planpath)
expected={x['module']:x['sha256'] for x in plan['artifacts']}
assert a.module in expected and sha(src)==expected[a.module]
helper=H/'scripts/native_resources.py'
assert sha(helper)==plan['recovery_v2']['resource_helper_sha256']
pre_gate=resources();assert not pre_gate['errors'] and pre_gate['free_bytes']>=1.5*1024**3 and not pre_gate['processes'],pre_gate
build=H/'build';build.mkdir(exist_ok=True)
stable=build/(a.module.replace('.','/')+'.olean');assert not stable.exists(),stable
env=os.environ.copy();env['PATH']=str(B)+';'+env['PATH'];external=[Path(p) for p in plan['external_library_search_paths']]
env['LEAN_PATH']=';'.join(map(str,[build,R/'milestones/148-actual-snake-share-transfer/build',Q/'build']+external))
start=time.monotonic();stamp=str(time.time_ns())
folder=H/'logs'/(a.module+'-'+stamp);folder.mkdir(parents=True)
log=folder/'compiler.log';rec=folder/'record.json'
(folder/'source.lean.txt').write_bytes(src.read_bytes());(folder/'checker.py.txt').write_bytes(Path(__file__).read_bytes())
deps={str(planpath):sha(planpath),str(B/'lean.exe'):sha(B/'lean.exe'),str(helper):sha(helper)}
version=subprocess.check_output([str(B/'lean.exe'),'--version'],env=env,cwd=R,text=True).strip()
assert version.startswith('Lean (version 4.19.0'),version
direct=subprocess.check_output([str(B/'lean.exe'),'--deps',str(src)],env=env,cwd=R,text=True).splitlines()
for name in re.findall(r'^import ([\w.]+)$',source,re.M):
    if name=='Std' or name.startswith('Mathlib.'):continue
    if name in plan['inherited_modules']:
        item=plan['inherited_modules'][name];rp=Path(item['receipt'])
        assert sha(rp)==item['receipt_sha256'];q=read(rp)
        assert q['status']=='PASS_PINNED_HISTORICAL_DATA_OBJECT_REUSE' and not q['fresh_compilation']
        deps[str(rp)]=sha(rp)
        for p,d in q['source_files_sha256'].items():
            assert sha(p)==d,p;deps[p]=d
        continue
    rp=H/'data'/(name+'-audit.json')
    if not rp.exists():rp=R/'milestones/148-actual-snake-share-transfer/data'/(name+'-audit.json')
    if not rp.exists():rp=Q/'data'/(name+'-audit.json')
    q=read(rp)
    assert q['status']=='PASS' and q['exit_code']==0 and q['stop_reason'] is None
    assert sha(q['source'])==q['source_sha256'] and sha(q['object'])==q['olean_sha256']
    deps[str(rp)]=sha(rp);deps[q['source']]=q['source_sha256'];deps[q['object']]=q['olean_sha256']
    for p,d in q['dependencies'].items():
        assert sha(p)==d,p;deps[p]=d
for p,d in plan['external_pins'].items():
    assert sha(p)==d,p;deps[p]=d
for value in direct:
    p=Path(value).resolve();assert p.is_file(),p
    assert any(p.is_relative_to(q.resolve()) for q in [build,R/'milestones/148-actual-snake-share-transfer/build',Q/'build',B.parent/'lib/lean']+external),p
    deps[str(p)]=sha(p)
gate=resources();assert not gate['errors'] and gate['free_bytes']>=1.5*1024**3 and len(gate['processes'])==0,gate
generic=a.module in plan['framework_modules']
obj=stable.with_name(stable.stem+'.'+stamp+'.olean');obj.parent.mkdir(parents=True,exist_ok=True)
state=dict(status='RUNNING',pid=os.getpid(),module=a.module,source=str(src),source_sha256=sha(src),
    checker_sha256=sha(__file__),dependencies=deps,toolchain_version=version,direct_dependencies=direct,
    stdlib_scope='Lean4.19 and Mathlib libraries are trusted; compiler, direct library objects, selected entry sources and library manifest are pinned. Generic clause models are reused from147 and coordinate/reversal helpers from148 with pinned receipts. The148 closure includes one historically compiled data object. The shared153 core and broader154 clause interpretation and conditional transfer are freshly checked; the single153 core contradiction remains separate.',
    resource_gate=gate,resource_samples=[],timeout_seconds=a.timeout,memory_limit_bytes=3*1024**3,
    minimum_free_bytes=768*1024**2,compiler_threads=1 if generic else 2,
    compiler_stack_kb=8192 if generic else 65536,
    preflight_seconds=time.monotonic()-start,log=str(log),paths=[str(build),str(Q/'build')]+list(map(str,external)))
def save():rec.write_text(json.dumps(state,indent=2)+'\n',encoding='utf-8',newline='\n')
cmd=[str(B/'lean.exe'),'-j',str(state['compiler_threads']),'-s',str(state['compiler_stack_kb'])]
cmd+=['-R',str(src.parent),'-o',str(obj),str(src)]
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
