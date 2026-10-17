"""Source-only, resumable reconstruction of the entire unconditional 244 chain.

Only the pinned standard toolchain/mathlib may supply prebuilt dependencies.
No custom object is copied from a development or earlier research build.
"""
from datetime import datetime,timezone
import hashlib,importlib.util,json,os,pathlib,re,shutil,subprocess,sys,tempfile,time
from resource_limits import run_bounded
from export_certificate import emit as emit_certificate
from generate_bridge import emit as emit_geometry
ROOT=pathlib.Path(__file__).resolve().parents[2]
HERE=ROOT/'work/window244'
PIN='c44e0c8ee63ca166450922a373c7409c5d26b00b'
ALLOWED={'propext','Classical.choice','Quot.sound'}
BRIDGE=['WindowGeometry','WindowCounters','WindowAlpha','WindowClauses','WindowReversal','WindowPermutation','CoordinateExtension','WindowNormalization']
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def now():return datetime.now(timezone.utc).isoformat()

def run(mathlib,resume=None):
    mathlib=pathlib.Path(mathlib).resolve()
    lake=shutil.which('lake');assert lake,'Put Lean 4.19.0 on PATH'
    lean=pathlib.Path(lake).with_name('lean.exe' if os.name=='nt' else 'lean')
    assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=mathlib,text=True).strip()==PIN
    subprocess.run(['git','diff','--exit-code','HEAD','--','*.lean','lean-toolchain','lake-manifest.json'],cwd=mathlib,check=True)
    assert 'version 4.19.0' in subprocess.check_output([str(lean),'--version'],text=True)
    base_dir=ROOT/'work/spectral/.verification';base_dir.mkdir(exist_ok=True)
    build=pathlib.Path(resume).resolve() if resume else pathlib.Path(tempfile.mkdtemp(prefix='window244-',dir=base_dir)).resolve()
    assert build.is_relative_to(base_dir.resolve()) and build.name.startswith('window244-')
    core=build/'core';logs=build/'logs';core.mkdir(exist_ok=True);logs.mkdir(exist_ok=True)
    guard=(build/'build.lock').open('a+b')
    guard.write(b'0');guard.flush();guard.seek(0)
    if os.name=='nt':
        import msvcrt
        msvcrt.locking(guard.fileno(),msvcrt.LK_NBLCK,1)
    else:
        import fcntl
        fcntl.flock(guard,fcntl.LOCK_EX|fcntl.LOCK_NB)
    manifest=build/'manifest.json'
    state=json.loads(manifest.read_text()) if manifest.exists() else dict(modules={},source_sha256={},axioms={})
    assert state.get('mathlib_commit',PIN)==PIN
    state.update(status='RUNNING',started_utc=state.get('started_utc',now()),mathlib_commit=PIN,
                 lean_sha256=sha(lean),build_directory=str(build),scope='SOURCE_ONLY_CUSTOM_CHAIN',pid=os.getpid())
    state.pop('error',None)
    state['driver_sha256']={p.relative_to(ROOT).as_posix():sha(p) for p in
        [HERE/'fresh_rebuild.py',HERE/'resource_limits.py',HERE/'export_certificate.py',HERE/'generate_bridge.py',ROOT/'work/spectral/verify_strengthened.py']}
    def save():
        tmp=manifest.with_suffix('.tmp');tmp.write_text(json.dumps(state,indent=2)+'\n');tmp.replace(manifest)
    def copy(src,dst):
        state['source_sha256'][src.relative_to(ROOT).as_posix()]=sha(src)
        shutil.copy2(src,dst);assert sha(src)==sha(dst)
    def audit(output):
        audits={n:[x.strip() for x in raw.split(',') if x.strip()] for n,raw in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",output)}
        assert all(set(a)<=ALLOWED for a in audits.values()),audits
        state['axioms'].update(audits)
        return audits
    save()
    print('Source-only build:',build,flush=True)
    try:
        for src in (ROOT/'work/final_lean').iterdir():
            if src.suffix=='.lean' or src.name in ['lakefile.toml','lake-manifest.json','lean-toolchain']:copy(src,core/src.name)
        env=os.environ.copy();env.pop('LEAN_PATH',None)
        # These are precisely the needed foundation roots; no KEEP bank is built.
        state['active']='core';save()
        with (logs/'core.log').open('w',encoding='utf-8') as log:
            result=subprocess.run([lake,'build','SingletonSquareLemma','OptimalityTarget','BallClauseLogic','DfsPrefix'],cwd=core,env=env,stdout=log,stderr=subprocess.STDOUT)
        assert result.returncode==0,'Foundation build failed; see core.log'
        state['core_olean_sha256']={p.relative_to(core).as_posix():sha(p) for p in sorted((core/'.lake/build/lib/lean').rglob('*.olean'))}
        state['core_log_sha256']=sha(logs/'core.log');save()
        spec=importlib.util.spec_from_file_location('strengthened_module_plan',ROOT/'work/spectral/verify_strengthened.py')
        baseline=importlib.util.module_from_spec(spec);spec.loader.exec_module(baseline)
        sources=[ROOT/'work/spectral/SquareIncidence.lean']+[ROOT/f'work/spectral/stronger/{n}.lean' for n in baseline.MODULES]
        sources += [ROOT/'work/lean112/LocalRup.lean',ROOT/'work/lean112/TreeRup.lean']+[HERE/(n+'.lean') for n in BRIDGE]
        for shape in ['repeated','distinct']:
            sources += [HERE/'generated'/(n+'.lean') for n in emit_certificate(shape)]
            sources += [HERE/'generated'/(n+'.lean') for n in emit_geometry(shape)]
        sources += [HERE/'Window223Exclusion.lean',HERE/'UpperBound244.lean']
        for src in sources:
            if src.is_relative_to(HERE):
                assert not re.search(r'\b(sorry|admit|native_decide|bv_decide)\b|^\s*axiom\s',src.read_text(encoding='utf-8'),re.M),src
            copy(src,build/src.name)
        env['LEAN_PATH']=os.pathsep.join(map(str,[core/'.lake/build/lib/lean',build]))
        env['LEAN_PATH']=subprocess.check_output([lake,'env',sys.executable,'-c',"import os;print(os.environ['LEAN_PATH'])"],cwd=mathlib,env=env,text=True).strip()
        state['module_order']=[s.stem for s in sources];save()
        for original in sources:
            name=original.stem;src=build/original.name;obj=build/(name+'.olean');logpath=logs/(name+'.log')
            deps={}
            for line in src.read_text(encoding='utf-8').splitlines():
                if line.startswith('import '):
                    for dep in line.split()[1:]:
                        if dep.startswith(('Mathlib','Std','Lean','Init')):continue
                        depobj=next(p for p in [build/(dep+'.olean'),core/'.lake/build/lib/lean'/(dep+'.olean')] if p.exists())
                        deps[dep]=sha(depobj)
            identity=dict(source_sha256=sha(src),imports=deps,lean_sha256=sha(lean))
            prior=state['modules'].get(name,{})
            if prior.get('identity')==identity and prior.get('exit_code')==0 and obj.exists() and prior.get('olean_sha256')==sha(obj) and logpath.exists() and prior.get('log_sha256')==sha(logpath):
                audit(logpath.read_text(encoding='utf-8'))
                continue
            state['active']=name;save();start=time.monotonic()
            with logpath.open('w',encoding='utf-8') as log:
                if original.is_relative_to(HERE) or name in ['LocalRup','TreeRup']:
                    rec=run_bounded([str(lean),'-j','1','--root='+str(build),'-o',str(obj),str(src)],log,cwd=build,env=env)
                else:
                    r=subprocess.run([str(lean),'-j','1','--root='+str(build),'-o',str(obj),str(src)],cwd=build,env=env,stdout=log,stderr=subprocess.STDOUT)
                    rec=dict(exit_code=r.returncode)
            output=logpath.read_text(encoding='utf-8');rec.update(identity=identity,seconds=time.monotonic()-start,log_sha256=sha(logpath))
            if not rec['exit_code']:rec['olean_sha256']=sha(obj)
            state['modules'][name]=rec;save()
            if rec['exit_code']:raise RuntimeError(f'{name} failed; see {logpath}')
            audit(output);save();print(name,'PASS',flush=True)
        final=build/'FinalAudit.lean'
        targets=['Snake9.no_two_two_three_internal','Snake9.no_three_two_two_internal','Snake9.upper_bound_244','Snake9.verified_interval_191_244']
        final.write_text('import UpperBound244\n'+''.join('#print axioms '+n+'\n' for n in targets),encoding='utf-8')
        result=subprocess.run([str(lean),'--root='+str(build),str(final)],cwd=build,env=env,capture_output=True,text=True,encoding='utf-8')
        (logs/'FinalAudit.log').write_text(result.stdout+result.stderr,encoding='utf-8')
        assert result.returncode==0,'Final audit failed'
        audits=audit(result.stdout);assert set(targets)<=audits.keys()
        # Detect source edits made while this long build was running.
        assert all(sha(ROOT/p)==h for p,h in state['source_sha256'].items()),'Sources changed during build'
        state.update(status='SUCCESS_191_244',active=None,completed_utc=now(),final_audit_sha256=sha(logs/'FinalAudit.log'))
        print('Verified 191 <= a(9) <= 244; exact optimum unresolved.',flush=True)
    except BaseException as exc:
        state.update(status='FAILED',error=str(exc));raise
    finally:
        save()
        guard.close()
