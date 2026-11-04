"""Check or reuse five rational implications with no concurrent Lean."""
from pathlib import Path
import hashlib, json, os, re, subprocess, sys, time

H=Path(__file__).resolve().parents[1]; A=H/'lean'; R=H.parents[1]
sys.path.insert(0,str(H/'scripts'))
from native_resources import snapshot
read=lambda p: json.loads(Path(p).read_text(encoding='utf-8-sig'))
sha=lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert not (R/'work/fullgraph-active.lock').exists()
assert not list((R/'milestones').glob('*/data/fullgraph.lock'))
planpath=R/'milestones/155-share17-replay/data/final-composition-plan.json'
assert planpath.exists()
plan=read(planpath)
helper=H/'scripts/native_resources.py'; assert sha(helper)==plan['resource_helper_sha256']
receipt=H/'data/affine-lean-check.json'
if receipt.exists():
    accepted=read(receipt)
    assert accepted['status']=='PASS' and accepted['exit_code']==0 and accepted['stop_reason'] is None
    for p,d in accepted['dependencies'].items():assert sha(p)==d,p
    assert sha(accepted['log'])==accepted['log_sha256']
    assert sha(accepted['object'])==accepted['olean_sha256']
    assert len(accepted['axioms'])==5
    assert all(set(row['axioms'])<={'propext','Classical.choice','Quot.sound'} for row in accepted['axioms'])
    print('PASS_REUSED_AFFINE_ARITHMETIC');raise SystemExit(0)
gate=snapshot(); assert not gate['errors'] and not gate['processes'] and gate['free_bytes']>=1.5*1024**3,gate
src=A/'AffineObstruction157.lean'; source=src.read_text(encoding='utf-8')
assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b',source)
B=Path('D:/Codex/2026-10-01/it-should-have-a-property-of/work/lean-research/lean-4.19.0-windows/bin')
env=os.environ.copy(); env['PATH']=str(B)+';'+env['PATH']
env['LEAN_PATH']=';'.join(plan['external_library_search_paths'])
deps={str(p):sha(p) for p in [src,Path(__file__),helper,B/'lean.exe']}
for path,digest in plan['external_pins'].items():
    assert sha(path)==digest; deps[path]=digest
direct=subprocess.check_output([str(B/'lean.exe'),'--deps',str(src)],cwd=R,env=env,text=True).splitlines()
for name in direct:
    path=Path(name).resolve(); assert path.is_file(); deps[str(path)]=sha(path)
stamp=str(time.time_ns()); folder=H/'logs'/('AffineObstruction157-'+stamp);folder.mkdir(parents=True)
(folder/'source.lean.txt').write_bytes(src.read_bytes())
(folder/'checker.py.txt').write_bytes(Path(__file__).read_bytes())
obj=folder/'AffineObstruction157.olean'; log=folder/'compiler.log'
cmd=[str(B/'lean.exe'),'-j','1','-s','8192','-R',str(A),'-o',str(obj),str(src)]
state=dict(status='RUNNING',source=str(src),source_sha256=sha(src),dependencies=deps,
    command=cmd,log=str(log),resource_gate=gate,resource_samples=[],scope='Five rational implications under explicit transformed edge and range inequalities; no graph feasibility claim.')
start=time.monotonic(); stop=None
with log.open('w',encoding='utf-8') as out:
    child=subprocess.Popen(cmd,cwd=R,env=env,stdout=out,stderr=subprocess.STDOUT)
    while child.poll() is None:
        sample=snapshot();state['resource_samples'].append(sample)
        if sample['errors']:stop='RESOURCE_QUERY_FAILED'
        if sample['free_bytes']<768*1024**2:stop='LOW_FREE_MEMORY'
        if any(x['ProcessId']!=child.pid for x in sample['processes']):stop='OTHER_LEAN_PROCESS'
        if any(x['PrivatePageCount']>3*1024**3 for x in sample['processes'] if x['ProcessId']==child.pid):stop='MEMORY_LIMIT'
        if time.monotonic()-start>60:stop='TIMEOUT'
        if stop:
            subprocess.run(['taskkill','/PID',str(child.pid),'/T','/F'],stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL);break
        time.sleep(1)
    code=child.wait(timeout=30)
output=log.read_text(encoding='utf-8')
reports=[dict(theorem=n,axioms=re.findall(r'[A-Za-z][\w.]*',xs))
    for n,xs in re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",output,re.S)]
reports += [dict(theorem=n,axioms=[]) for n in re.findall(r"'([^']+)' does not depend on any axioms",output)]
expected={'Snake9.AffineObstruction157.'+n for n in ['affine_margin','affine_comparison','weaker_walk_range','target_range','transferred_comparison']}
ok=code==0 and stop is None and 'error:' not in output and 'sorryAx' not in output
ok=ok and len(reports)==5 and {x['theorem'] for x in reports}==expected
ok=ok and all(set(x['axioms'])<={'propext','Classical.choice','Quot.sound'} for x in reports)
ok=ok and all(sha(p)==d for p,d in deps.items())
state.update(status='PASS' if ok else 'FAILED',exit_code=code,stop_reason=stop,
    seconds=time.monotonic()-start,axioms=reports,log_sha256=sha(log))
if ok:state.update(object=str(obj),olean_sha256=sha(obj))
(folder/'record.json').write_text(json.dumps(state,indent=2)+'\n',encoding='utf-8',newline='\n')
if ok:receipt.write_bytes((folder/'record.json').read_bytes())
print(json.dumps({k:state[k] for k in ['status','seconds','axioms','stop_reason']}))
raise SystemExit(0 if ok else 1)
