"""Resumable parallel development checks of the selected Stage-2 cases.

Uses only the verified Stage-1 foundation as a development cache. A future
stronger global bound still requires its own full source-only rebuild.
"""
import argparse,concurrent.futures,hashlib,json,os,pathlib,re,subprocess,sys,time
from resource_limits import run_bounded
from stage2_export import emit as emit_proof
import generate_bridge
ROOT=pathlib.Path(__file__).resolve().parents[2]
OUT=ROOT/'outputs/window244/stage2';CACHE=OUT/'cache';LOG=OUT/'lean-logs'
SOURCES=ROOT/'work/window244/stage2_generated'
for p in [CACHE,LOG,SOURCES]:p.mkdir(parents=True,exist_ok=True)
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--foundation',type=pathlib.Path,required=True)
parser.add_argument('--mathlib-dir',type=pathlib.Path,required=True)
parser.add_argument('--lean-bin',type=pathlib.Path,required=True)
parser.add_argument('--jobs',type=int,default=2)
args=parser.parse_args();foundation=args.foundation.resolve();mathlib=args.mathlib_dir.resolve()
lean=args.lean_bin.resolve()/('lean.exe' if os.name=='nt' else 'lean')
lake=lean.with_name('lake.exe' if os.name=='nt' else 'lake')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def save(p,s):
    tmp=p.with_suffix('.tmp');tmp.write_bytes((json.dumps(s,indent=2)+'\n').encode());tmp.replace(p)
guard=(OUT/'lean-build.lock').open('a+b');guard.write(b'0');guard.flush();guard.seek(0)
if os.name=='nt':
    import msvcrt
    msvcrt.locking(guard.fileno(),msvcrt.LK_NBLCK,1)
else:
    import fcntl
    fcntl.flock(guard,fcntl.LOCK_EX|fcntl.LOCK_NB)
base=json.loads((foundation/'manifest.json').read_text());assert base['status']=='SUCCESS_191_244'
for n in ['LocalRup','TreeRup','WindowClauses','WindowAlpha']:
    assert sha(foundation/(n+'.olean'))==base['modules'][n]['olean_sha256']
cert=json.loads((OUT/'certificates/manifest.json').read_text())
assert cert['status']=='PASSED_EXECUTABLE_REPLAY_ONLY'
env=os.environ.copy();env['LEAN_PATH']=os.pathsep.join(map(str,[CACHE,foundation,foundation/'core/.lake/build/lib/lean']))
raw=subprocess.check_output([str(lake),'env',sys.executable,'-c',"import os;print(os.environ['LEAN_PATH'])"],cwd=mathlib,env=env,text=True).strip()
env['LEAN_PATH']=os.pathsep.join(str((mathlib/pathlib.Path(p)).resolve()) for p in raw.split(os.pathsep) if p)
generate_bridge.OUT=SOURCES
cases=[]
for pattern in cert['chosen_patterns']:
    for shape in ['repeated','distinct']:
        digits=''.join(map(str,pattern));key=digits+'-'+shape;prefix='W242P'+digits+shape.title()
        core=OUT/'certificates'/(key+'_core.json');model=OUT/'certificates'/(key+'.json')
        assert sha(core)==cert['cases'][key]['core_sha256']
        modules=emit_proof(shape,core,prefix,SOURCES)
        modules+=generate_bridge.emit(shape,model,core,prefix)
        cases.append((key,prefix,modules,core,model))
coordinator=OUT/'lean-build.json';state=dict(status='RUNNING',pid=os.getpid(),jobs=args.jobs,
    cases={k:'PENDING' for k,*_ in cases},scope='DEVELOPMENT_CASE_CHECKS_ONLY; no new global bound')
save(coordinator,state)
def check_case(case):
    key,prefix,modules,core,model=case
    path=OUT/(key+'-lean.json');record=json.loads(path.read_text()) if path.exists() else dict(modules={})
    record.update(status='RUNNING',active=None,pid=os.getpid(),module_order=modules,
        core_sha256=sha(core),model_sha256=sha(model),lean_sha256=sha(lean),foundation=str(foundation))
    record.pop('error',None);save(path,record)
    try:
        for name in modules:
            src=SOURCES/(name+'.lean');obj=CACHE/(name+'.olean');logpath=LOG/(name+'.log')
            text=src.read_text(encoding='utf-8')
            assert not re.search(r'\b(sorry|admit|native_decide|bv_decide)\b|^\s*axiom\s',text,re.M),name
            deps={}
            for line in text.splitlines():
                if line.startswith('import '):
                    for dep in line.split()[1:]:
                        if dep.startswith(('Mathlib','Std','Lean','Init')):continue
                        depobj=next(p for p in [CACHE/(dep+'.olean'),foundation/(dep+'.olean'),foundation/'core/.lake/build/lib/lean'/(dep+'.olean')] if p.exists())
                        deps[dep]=sha(depobj)
            identity=dict(source_sha256=sha(src),imports=deps,lean_sha256=sha(lean))
            old=record['modules'].get(name,{})
            if old.get('identity')==identity and old.get('exit_code')==0 and obj.exists() and sha(obj)==old.get('olean_sha256') and logpath.exists() and sha(logpath)==old.get('log_sha256'):continue
            record['active']=name;save(path,record);tick=time.monotonic()
            with logpath.open('w',encoding='utf-8') as log:
                result=run_bounded([str(lean),'-j','1','--root='+str(SOURCES),'-o',str(obj),str(src)],log,cwd=ROOT,env=env)
            output=logpath.read_text(encoding='utf-8')
            audits={n:[x.strip() for x in a.split(',') if x.strip()] for n,a in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",output)}
            result.update(identity=identity,seconds=time.monotonic()-tick,log_sha256=sha(logpath),axioms=audits)
            if not result['exit_code']:result['olean_sha256']=sha(obj)
            record['modules'][name]=result;save(path,record)
            if result['exit_code'] or any(set(a)-{'propext','Classical.choice','Quot.sound'} for a in audits.values()):raise RuntimeError(output[-4000:])
            print(key,name,'PASS',flush=True)
        record.update(status='PASSED_BOOLEAN_AND_STANDARD_GEOMETRY_ONLY',active=None);save(path,record)
        return record['status']
    except BaseException as exc:
        record.update(status='FAILED',error=str(exc));save(path,record);raise
try:
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as pool:
        futures={pool.submit(check_case,c):c[0] for c in cases}
        for future in concurrent.futures.as_completed(futures):
            key=futures[future]
            try:state['cases'][key]=future.result()
            except Exception as exc:state['cases'][key]='FAILED';state.setdefault('errors',{})[key]=str(exc)
            save(coordinator,state)
    state['status']='FAILED_CASES' if state.get('errors') else 'PASSED_DEVELOPMENT_CASES_ONLY'
    save(coordinator,state)
finally:guard.close()
