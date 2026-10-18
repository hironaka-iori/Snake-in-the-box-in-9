"""Independent source-only reconstruction of the pinned upstream 241 result.

Only the target's transitive custom import closure is extracted from Git.
No source checkout or already verified 244 evidence is changed. No upstream
compiled custom object is used. The original 1800 MiB budget is retained.
"""
import argparse,hashlib,json,os,pathlib,re,subprocess,sys,time
from datetime import datetime,timezone
from resource_limits import run_bounded
ROOT=pathlib.Path(__file__).resolve().parents[2]
REV='7d418905e17fd2ea0d4666682f0019789490236a'
PIN='c44e0c8ee63ca166450922a373c7409c5d26b00b'
ALLOWED={'propext','Classical.choice','Quot.sound'}
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--lean-bin',type=pathlib.Path,required=True)
parser.add_argument('--mathlib-dir',type=pathlib.Path,required=True)
args=parser.parse_args()
build=ROOT/'work/spectral/.verification/upstream241-7d41890'
logs=build/'logs';logs.mkdir(parents=True,exist_ok=True)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def now():return datetime.now(timezone.utc).isoformat()
def git(*command):return subprocess.check_output(['git',*command],cwd=ROOT)
lean=args.lean_bin.resolve()/('lean.exe' if os.name=='nt' else 'lean')
lake=lean.with_name('lake.exe' if os.name=='nt' else 'lake');mathlib=args.mathlib_dir.resolve()
assert 'version 4.19.0' in subprocess.check_output([str(lean),'--version'],text=True)
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=mathlib,text=True).strip()==PIN
subprocess.run(['git','diff','--exit-code','HEAD','--','*.lean','lean-toolchain','lake-manifest.json'],cwd=mathlib,check=True)
assert git('rev-parse',REV).decode().strip()==REV
guard=(build/'build.lock').open('a+b');guard.write(b'0');guard.flush();guard.seek(0)
if os.name=='nt':
    import msvcrt
    msvcrt.locking(guard.fileno(),msvcrt.LK_NBLCK,1)
else:
    import fcntl
    fcntl.flock(guard,fcntl.LOCK_EX|fcntl.LOCK_NB)
manifest=build/'manifest.json'
state=json.loads(manifest.read_text()) if manifest.exists() else dict(modules={},sources={})
assert state.get('upstream_commit',REV)==REV
state.update(status='RUNNING',pid=os.getpid(),upstream_commit=REV,mathlib_commit=PIN,
    started_utc=state.get('started_utc',now()),lean_sha256=sha(lean),
    scope='SOURCE_ONLY_UPSTREAM_241_IMPORT_CLOSURE',driver_sha256=sha(pathlib.Path(__file__)))
state.pop('error',None)
def save():
    tmp=manifest.with_suffix('.tmp');tmp.write_bytes((json.dumps(state,indent=2)+'\n').encode());tmp.replace(manifest)
save()
print('Independent build:',build,flush=True)
try:
    roots=['work/final_lean/','work/spectral/stronger/','work/spectral/']
    paths=git('ls-tree','-r','--name-only',REV,'--','work/final_lean','work/spectral').decode().splitlines()
    mapping={}
    for prefix in roots:
        for path in paths:
            if path.startswith(prefix) and path.endswith('.lean'):
                rel=path[len(prefix):]
                if prefix=='work/spectral/' and '/' in rel:continue
                mapping.setdefault(rel[:-5].replace('/','.'),path)
    order=[];deps={};visiting=set();done=set()
    batch=subprocess.Popen(['git','cat-file','--batch'],cwd=ROOT,stdin=subprocess.PIPE,stdout=subprocess.PIPE)
    def read_blob(path):
        batch.stdin.write((REV+':'+path+'\n').encode());batch.stdin.flush()
        header=batch.stdout.readline().split();assert len(header)==3 and header[1]==b'blob',header
        raw=batch.stdout.read(int(header[2]));assert batch.stdout.read(1)==b'\n'
        return raw
    def visit(name):
        if name in done:return
        assert name not in visiting,'Import cycle: '+name
        visiting.add(name)
        if name not in mapping:raise RuntimeError('Unresolved custom import: '+name)
        raw=read_blob(mapping[name]);upstream_sha=hashlib.sha256(raw).hexdigest()
        if name in {'Snake9','SquareCounterexample'}:
            # Preserve every definition and theorem statement. Kernel reduction
            # avoids elaborating the enormous default `decide` proof term.
            original=raw.decode('utf-8')
            if name=='Snake9':
                assert original==(ROOT/'work/final_lean/Snake9.lean').read_text(encoding='utf-8')
                assert original.count(':= by decide')==2
            size=192 if name=='Snake9' else 138
            # Split the outer finite quantifier: each kernel check has only
            # 192 pairs, instead of a single 192-by-192 reduction.
            for label,predicate in [
                ('distinct','witnessVertex i = witnessVertex j → i = j'),
                ('induced','i.val < j.val → (Adj (witnessVertex i) (witnessVertex j) ↔ i.val + 1 = j.val)')]:
                rows=[]
                for i in range(size):
                    prop=predicate.replace('witnessVertex i',f'witnessVertex ({i} : Fin {size})').replace('i.val',f'({i} : Fin {size}).val').replace('i = j',f'({i} : Fin {size}) = j')
                    rows.append(f'theorem witness_{label}_row_{i} : ∀ j : Fin {size}, {prop} := by decide +kernel\n')
                term='(fun i => Fin.elim0 i)'
                for i in reversed(range(size)):
                    term=f'(Fin.cases witness_{label}_row_{i} {term})'
                pattern=r'theorem witness_'+label+r'\s*:[\s\S]*?:= by decide'
                match=re.search(pattern,original);assert match
                replacement='\n'.join(rows)+'\n'+match.group(0).replace('by decide',f'by\n  exact {term}')
                original=original[:match.start()]+replacement+original[match.end():]
            original=original.replace('-- BEGIN WITNESS','-- BEGIN WITNESS\nset_option Elab.async false')
            if name=='SquareCounterexample':
                original=original.replace('set_option maxHeartbeats 0','set_option maxHeartbeats 0\nset_option Elab.async false')
                original=original.replace(':= by decide\n',':= by decide +kernel\n')
            raw=original.encode('utf-8')
        src=build/(name.replace('.','/')+'.lean')
        src.parent.mkdir(parents=True,exist_ok=True)
        if not src.exists() or src.read_bytes()!=raw:src.write_bytes(raw)
        state['sources'][name]=dict(git_path=mapping[name],sha256=sha(src),upstream_sha256=upstream_sha,
            adaptation=(f'two witness proofs: {size} kernel-checked rows and Fin.cases each' if name in {'Snake9','SquareCounterexample'} else None))
        imports=[]
        for line in raw.decode('utf-8').splitlines():
            if line.startswith('import '):
                imports.extend(line.split('--',1)[0].split()[1:])
        deps[name]=[n for n in imports if n.split('.')[0] not in {'Mathlib','Std','Lean','Init','Batteries','Qq','Aesop'}]
        for dep in deps[name]:visit(dep)
        visiting.remove(name);done.add(name);order.append(name)
    try:visit('UpperBound241')
    finally:
        batch.stdin.close();batch.stdout.close();batch.wait()
    state.update(module_order=order,dependencies=deps);save()
    print('Source closure:',len(order),'modules',flush=True)
    env=os.environ.copy();env['LEAN_PATH']=str(build)
    raw=subprocess.check_output([str(lake),'env',sys.executable,'-c',"import os;print(os.environ['LEAN_PATH'])"],cwd=mathlib,env=env,text=True).strip()
    env['LEAN_PATH']=os.pathsep.join(str((mathlib/pathlib.Path(p)).resolve()) for p in raw.split(os.pathsep) if p)
    state['lean_path']=env['LEAN_PATH'].split(os.pathsep);save()
    for name in order:
        src=build/(name.replace('.','/')+'.lean');obj=src.with_suffix('.olean')
        logpath=logs/(name+'.log')
        identity=dict(source_sha256=sha(src),lean_sha256=sha(lean),
            imports={dep:sha(build/(dep.replace('.','/')+'.olean')) for dep in deps[name]})
        old=state['modules'].get(name,{})
        if old.get('identity')==identity and old.get('exit_code')==0 and obj.exists() and sha(obj)==old.get('olean_sha256') and logpath.exists() and sha(logpath)==old.get('log_sha256'):continue
        state['active']=name;save();tick=time.monotonic()
        with logpath.open('w',encoding='utf-8') as log:
            rec=run_bounded([str(lean),'-j','1','--root='+str(build),'-o',str(obj),str(src)],log,cwd=build,env=env)
        output=logpath.read_text(encoding='utf-8')
        audits={n:[a.strip() for a in text.split(',') if a.strip()] for n,text in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",output)}
        rec.update(identity=identity,seconds=time.monotonic()-tick,log_sha256=sha(logpath),axioms=audits)
        if not rec['exit_code']:rec['olean_sha256']=sha(obj)
        state['modules'][name]=rec;save()
        if rec['exit_code'] or any(set(a)-ALLOWED for a in audits.values()):raise RuntimeError(name+' failed: '+output[-3000:])
        print(name,'PASS',round(rec['seconds'],2),flush=True)
    audit=build/'IndependentAudit.lean'
    targets=['Snake9.upper_bound_242','Snake9.upper_bound_241','Snake9.verified_interval_191_241']
    audit.write_bytes(('import UpperBound241\n'+''.join('#print axioms '+n+'\n' for n in targets)).encode())
    with (logs/'IndependentAudit.log').open('w',encoding='utf-8') as log:
        rec=run_bounded([str(lean),'--root='+str(build),str(audit)],log,cwd=build,env=env)
    assert rec['exit_code']==0,'IndependentAudit failed'
    output=(logs/'IndependentAudit.log').read_text(encoding='utf-8')
    audits={n:[a.strip() for a in text.split(',') if a.strip()] for n,text in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",output)}
    assert set(targets)<=audits.keys() and all(set(a)<=ALLOWED for a in audits.values()),audits
    assert all(sha(build/(n.replace('.','/')+'.lean'))==v['sha256'] for n,v in state['sources'].items())
    state.update(status='SUCCESS_INDEPENDENT_191_241',active=None,completed_utc=now(),
        final_axioms=audits,final_audit_sha256=sha(logs/'IndependentAudit.log'))
    save();print('Independently verified 191 <= a(9) <= 241.',flush=True)
except BaseException as exc:
    state.update(status='FAILED',error=str(exc));save();raise
finally:guard.close()
