"""Check one continuation module using the accepted prefix checkpoint."""
from pathlib import Path
import argparse,hashlib,json,os,re,subprocess,time
from native_resources import snapshot
H=Path(__file__).resolve().parents[1];R=H.parents[1]
def sha(p):
    h=hashlib.sha256()
    with Path(p).open('rb') as f:
        for b in iter(lambda:f.read(1048576),b''):h.update(b)
    return h.hexdigest()
def retry(action):
    for attempt in range(40):
        try:return action()
        except PermissionError:
            if attempt==39:raise
            time.sleep(.05)
def read(p):return retry(lambda:json.loads(Path(p).read_text(encoding='utf-8-sig')))
def save(p,j):
    tmp=p.with_name(p.name+'.'+str(os.getpid())+'.tmp')
    retry(lambda:tmp.write_text(json.dumps(j,indent=2)+'\n',encoding='utf-8'))
    retry(lambda:os.replace(tmp,p))
ap=argparse.ArgumentParser();ap.add_argument('module');ap.add_argument('--timeout',type=int,default=60);a=ap.parse_args()
planpath=H/'data'/(a.module+'-execution.json');plan=read(planpath)
assert a.module in plan['new_module_order']
src=H/'lean'/(a.module.replace('.','/')+'.lean');source=src.read_text(encoding='utf-8')
assert sha(src)==plan['source_sha256'][a.module]
assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b',source)
for p,d in plan['input_pins'].items():assert sha(p)==d,p
assert sha(__file__)==plan['checker_sha256']
rp=H/'data'/(a.module+'-audit.json');stable=H/'build'/(a.module.replace('.','/')+'.olean')
if rp.exists():
    j=read(rp);assert j['status']=='PASS' and j['exit_code']==0 and j['stop_reason'] is None
    assert sha(src)==j['source_sha256'] and sha(stable)==j['olean_sha256']
    assert sha(j['log'])==j['log_sha256']
    for p,d in j['dependencies'].items():assert sha(p)==d,p
    assert len(j['axioms'])==source.count('#print axioms')
    print('REUSED',a.module);raise SystemExit(0)
assert not stable.exists(), 'Unrecorded object requires inspection.'
assert not (R/'work/fullgraph-active.lock').exists()
assert not list((R/'milestones').glob('*/data/fullgraph.lock'))
gate=snapshot();startup_deadline=time.monotonic()+55;startup_samples=[]
while gate['errors'] or gate['processes'] or gate['free_bytes']<1024**3:
    startup_samples.append(gate)
    if time.monotonic()>=startup_deadline:break
    time.sleep(1);gate=snapshot()
if startup_samples:
    save(H/'logs'/('proof-startup-'+str(time.time_ns())+'.json'),startup_samples+[gate])
assert not gate['errors'] and not gate['processes'] and gate['free_bytes']>=1024**3,gate
B=Path(plan['lean_bin']);env=os.environ.copy();env['PATH']=str(B)+';'+env['PATH'];env['LEAN_PATH']=';'.join(plan['search_paths'])
deps={str(planpath):sha(planpath),str(src):sha(src),str(Path(__file__)):sha(__file__)}
deps.update(plan['input_pins'])
for module in re.findall(r'^import ([\w.]+)$',source,re.M):
    if module.startswith('Mathlib.') or module=='Std':continue
    if module in plan['source_sha256'] and module!='LocalWindowCnf.ShareWindow144':
        qpath=H/'data'/(module+'-audit.json');q=read(qpath)
        assert q['status']=='PASS' and q['exit_code']==0 and q['stop_reason'] is None
        assert sha(q['source'])==q['source_sha256'] and sha(q['object'])==q['olean_sha256']
        assert sha(q['log'])==q['log_sha256']
        deps[str(qpath)]=sha(qpath)
        for p,d in q['dependencies'].items():assert sha(p)==d,p
for name in subprocess.check_output([str(B/'lean.exe'),'--deps',str(src)],env=env,cwd=R,text=True).splitlines():
    p=Path(name).resolve();assert p.is_file();deps[str(p)]=sha(p)
stamp=str(time.time_ns());folder=H/'logs'/(a.module+'-'+stamp);folder.mkdir(parents=True)
(folder/'source.lean.txt').write_bytes(src.read_bytes());(folder/'checker.py.txt').write_bytes(Path(__file__).read_bytes())
obj=folder/'module.olean';log=folder/'compiler.log'
cmd=[str(B/'lean.exe'),'-j','1','-s','8192','-R',str(H/'lean'),'-o',str(obj),str(src)]
j=dict(status='RUNNING',module=a.module,source=str(src),source_sha256=sha(src),checker_sha256=sha(__file__),dependencies=deps,command=cmd,log=str(log),resource_gate=gate,resource_samples=[])
start=time.monotonic();stop=None
with log.open('w',encoding='utf-8') as out:
    child=subprocess.Popen(cmd,cwd=R,env=env,stdout=out,stderr=subprocess.STDOUT)
    j['compiler_pid']=child.pid;save(folder/'record.json',j)
    while child.poll() is None:
        sample=snapshot();j['resource_samples'].append(sample)
        if sample['errors']:stop='RESOURCE_QUERY_FAILED'
        if sample['free_bytes']<768*1024**2:stop='LOW_FREE_MEMORY'
        if any(x['ProcessId']!=child.pid for x in sample['processes']):stop='OTHER_LEAN_PROCESS'
        if any(x['PrivatePageCount']>256*1024**2 for x in sample['processes'] if x['ProcessId']==child.pid):stop='MEMORY_LIMIT'
        if time.monotonic()-start>a.timeout:stop='TIMEOUT'
        if stop:
            child.terminate();break
        time.sleep(1)
    code=child.wait(timeout=30)
output=log.read_text(encoding='utf-8')
reports=[dict(theorem=n,axioms=re.findall(r'[A-Za-z][\w.]*',xs)) for n,xs in re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",output,re.S)]
reports += [dict(theorem=n,axioms=[]) for n in re.findall(r"'([^']+)' does not depend on any axioms",output)]
ok=code==0 and stop is None and 'error:' not in output and 'sorryAx' not in output
ok=ok and len(reports)==source.count('#print axioms') and all(set(x['axioms'])<={'propext','Classical.choice','Quot.sound'} for x in reports)
ok=ok and all(sha(p)==d for p,d in deps.items())
j.update(status='PASS' if ok else 'FAILED',exit_code=code,stop_reason=stop,seconds=time.monotonic()-start,axioms=reports,log_sha256=sha(log))
if ok:
    stable.parent.mkdir(parents=True,exist_ok=True);stable.write_bytes(obj.read_bytes());j.update(object=str(stable),olean_sha256=sha(stable))
save(folder/'record.json',j)
if ok:rp.write_bytes((folder/'record.json').read_bytes())
print(j['status'],a.module,'seconds',round(j['seconds'],3),'reason',stop,flush=True)
raise SystemExit(0 if ok else 1)
