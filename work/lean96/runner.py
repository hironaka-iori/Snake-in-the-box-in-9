"""Standalone resumable KEEP=96 Lean campaign. Never treats solver evidence as Lean."""
from common import *
import argparse,concurrent.futures,msvcrt,re,subprocess,threading,traceback,shutil
from export_local_rup import emit as emit_boolean
from generate_cover import emit as emit_cover,aggregate
import psutil

LEAN=Path(os.environ.get('LEAN96_LEAN','E:/work/Math/MATH PROJECT/.tools/lean-4.19.0-windows/bin/lean.exe'))
STD=LEAN.parent.parent/'lib/lean'
ENV=os.environ.copy();ENV.update(LEAN_PATH=str(CACHE),PYTHONUTF8='1')
AXIOMS={'propext','Classical.choice','Quot.sound'}
MUTEX=threading.RLock();PREP=threading.Semaphore(1)
STATE=read(OUT/'progress.json',dict(entries={},representatives={},failures={},active={},stages={},status='NOT_STARTED'))
RECORDS=read(OUT/'modules.json',{})
SURVEY=read(OUT/'survey.json',{})
COVER=read(OUT/'cover.json',{})
NATIVE=HERE/'.native/drat-trim.exe'

def publish():
    STATE['checkpoint_utc']=now();STATE['pid']=os.getpid()
    STATE['completed_entries']=len(STATE['entries']);STATE['completed_representatives']=len(STATE['representatives'])
    save(OUT/'progress.json',STATE)
    save(OUT/'modules.json',RECORDS)

def source(name):
    for folder in (BANK,HERE,ROOT/'work/final_lean'):
        p=folder/(name+'.lean')
        if p.exists():return p
    raise FileNotFoundError(name)

def dependencies(p):
    return [x for line in p.read_text(encoding='utf-8').splitlines() if line.startswith('import ') for x in line[7:].split()]

def object_path(name):
    if name=='Std' or name.startswith(('Std.','Lean.','Init.')) or name in ('Init','Lean'):
        return STD/(name.replace('.','/')+'.olean')
    return CACHE/(name+'.olean')

def audit(name,theorem):
    rec=RECORDS[name];log=ROOT/rec['log']
    assert sha(log)==rec['log_sha256']
    text=log.read_text(encoding='utf-8')
    pattern=r"'"+re.escape(theorem)+r"' depends on axioms: \[([^]]*)\]"
    match=re.search(pattern,text,re.S)
    if not match:
        if f"'{theorem}' does not depend on any axioms" in text:return []
        raise ValueError('Missing axiom audit: '+theorem)
    axes=set(x.strip() for x in match[1].split(',') if x.strip())
    if not axes<=AXIOMS:raise ValueError('Forbidden axioms: '+str(axes))
    return sorted(axes)

def limited(command,log,seconds=1800,memory=4096):
    with log.open('w',encoding='utf-8') as f:
        p=subprocess.run([sys.executable,'-X','utf8',str(HERE/'bounded.py'),str(memory),str(seconds),*map(str,command)],
            stdout=f,stderr=subprocess.STDOUT,cwd=ROOT,env=ENV)
    return p.returncode

def check(name,worker='setup',force=False):
    src=source(name);code=src.read_text(encoding='utf-8')
    # Scan executable source conservatively; imported trusted stdlib is separately pinned.
    if re.search(r'\b(sorry|admit|native_decide)\b|^\s*axiom\s',code,re.M):raise ValueError('Forbidden source token: '+name)
    deps={n:sha(object_path(n)) for n in dependencies(src)}
    fingerprint=sha(src);target=object_path(name)
    with MUTEX:
        STATE['active'][str(worker)]=dict(stage='LEAN',module=name,started=now());publish()
        rec=RECORDS.get(name,{})
    compiler=sha(LEAN)
    if not force and rec.get('status')=='PASSED' and rec.get('source_sha256')==fingerprint and rec.get('dependencies')==deps and rec.get('compiler_sha256')==compiler and target.exists() and sha(target)==rec.get('artifact_sha256') and sha(ROOT/rec['log'])==rec.get('log_sha256'):
        return rec
    folder=OUT/'logs'/name;folder.mkdir(exist_ok=True)
    log=folder/(str(time.time_ns())+'.log');t=time.monotonic()
    print('CHECK',name,flush=True)
    memory=12288 if name=='Snake9' else 4096
    rc=limited([LEAN,'-j','1','-s','16384','--root='+str(src.parent),'-o',target,src],log,memory=memory)
    output=log.read_text(encoding='utf-8')
    status='PASSED' if rc==0 else ('TIMEOUT' if rc==124 else ('RESOURCE_FAILURE' if any(x in output.lower() for x in ['out of memory','failed to create thread']) else 'COMPILATION_ERROR'))
    if sha(src)!=fingerprint or any(sha(object_path(n))!=h for n,h in deps.items()):raise ValueError('Inputs changed during compilation')
    rec=dict(status=status,returncode=rc,source=str(src.relative_to(ROOT)),source_sha256=fingerprint,dependencies=deps,
        compiler_sha256=compiler,memory_mib=memory,thread_stack_kib=16384,seconds=time.monotonic()-t,finished=now(),log=str(log.relative_to(ROOT)),log_sha256=sha(log))
    if rc==0:rec['artifact_sha256']=sha(target)
    save(log.with_suffix('.json'),rec)
    with MUTEX:RECORDS[name]=rec;publish()
    if rc:raise RuntimeError(name+' '+status+' '+log.read_text(encoding='utf-8')[-2500:])
    return rec

def setup():
    done=set()
    def build(name):
        if name in done or object_path(name).is_relative_to(STD):return
        for d in dependencies(source(name)):build(d)
        check(name);done.add(name)
    for name in ['LocalRup','TreeRup','Regrowth96ParityCounts','DfsBankData','CubeLocal']:build(name)
    if not NATIVE.exists():
        NATIVE.parent.mkdir(exist_ok=True)
        compiler=HERE/'.packages/ziglang/zig.exe';src=ROOT/'work/keep96/vendor/drat-trim/drat-trim.c'
        cmd=[compiler,'cc',src,'-O2','-std=c99','-Dgetc_unlocked=getc','-o',NATIVE]
        p=subprocess.run(list(map(str,cmd)),cwd=ROOT,capture_output=True,text=True,timeout=300)
        (OUT/'native-build.log').write_text(p.stdout+p.stderr,encoding='utf-8')
        if p.returncode:raise RuntimeError('Native checker build failed')
        save(OUT/'native-build.json',dict(command=list(map(str,cmd)),compiler_sha256=sha(compiler),source_sha256=sha(src),binary_sha256=sha(NATIVE)))
    if sha(NATIVE)!=read(OUT/'native-build.json')['binary_sha256']:raise ValueError('Native binary changed')
    with MUTEX:STATE['active'].pop('setup',None);publish()

def evidence(entry,trim_required=True):
    """Serialized prep bounds peak RAM. Each certificate and attempt is preserved."""
    with PREP:
        row=SURVEY['entries'][str(entry)]
        identity=dict(formula_sha256=sha(ROOT/row['formula']),cnf_sha256=sha(ROOT/row['cnf']),
            trimmer_sha256=sha(HERE/'trim.py'),trim_worker_sha256=sha(HERE/'trim_worker.py'),native_sha256=sha(NATIVE),trim_required=trim_required)
        cache=OUT/f'cores/entry{entry:03d}.receipt.json';prior=read(cache,{})
        if prior.get('identity')==identity and all((ROOT/p).exists() and sha(ROOT/p)==h for p,h in prior.get('artifacts',{}).items()) and prior.get('status')=='VERIFIED_TRIMMED_NOT_LEAN':return
        with MUTEX:STATE['active'][str(entry)]=dict(stage='CERTIFICATE_PREPARATION',started=now());publish()
        folder=OUT/'artifacts'/f'entry{entry:03d}'/str(time.time_ns());folder.mkdir(parents=True)
        cert=ROOT/row['certificate'] if row.get('certificate') else None
        if cert is None:
            # A changed trimmer must not trigger duplicate SAT search. Reuse a
            # successful local solver attempt only after checking its identities.
            for saved in sorted(folder.parent.glob('*/result.json'),reverse=True):
                result=read(saved,{})
                config=read(saved.parent/'config.json',{})
                candidate=ROOT/result.get('certificate','__missing__')
                if (result.get('status')=='UNSAT' and config.get('formula_sha256')==identity['formula_sha256']
                    and config.get('encoder_sha256')==sha(ROOT/'work/build_regrowth_cnf.py')
                    and candidate.is_file() and sha(candidate)==result.get('certificate_sha256')):
                    cert=candidate;break
        if not cert or not cert.exists():
            save(folder/'started.json',dict(entry=entry,formula_sha256=identity['formula_sha256'],solver_limit_seconds=300,memory_mib=2048,started=now()))
            rc=limited([sys.executable,'-X','utf8',HERE/'solver_worker.py',entry,folder],folder/'solver.log',300,2048)
            result=read(folder/'result.json',{})
            if rc or result.get('status')!='UNSAT':
                save(folder/'termination.json',dict(status='UNKNOWN_TIMEOUT' if rc==124 else result.get('status','RESOURCE_OR_PROCESS_FAILURE'),returncode=rc,time=now()))
                raise RuntimeError('Certificate regeneration unresolved for '+str(entry)+'; see '+str(folder))
            cert=ROOT/result['certificate']
        elif sha(cert)!=row['certificate_sha256']:raise ValueError('Historical certificate hash mismatch')
        with MUTEX:STATE['stages'][str(entry)]=dict(solver='UNSAT',native='PENDING',lean='PENDING');publish()
        cnf=folder/'input.cnf';proof=folder/'input.drup';lrat=folder/'proof.lrat'
        for src,dest in [(ROOT/row['cnf'],cnf),(cert,proof)]:
            with gzip.open(src,'rb') as inp,dest.open('wb') as f:shutil.copyfileobj(inp,f)
        native_log=folder/'native.log'
        rc=limited([NATIVE,cnf,proof,'-L',lrat,'-t','1800'],native_log,1800,4096)
        if rc or 's VERIFIED' not in native_log.read_text(encoding='utf-8'):raise RuntimeError('Native verification failed/timed out: '+str(entry))
        paths=[cert,cnf,proof,lrat,native_log]
        if trim_required:
            core=OUT/f'cores/entry{entry:03d}.json'
            rc=limited([sys.executable,'-X','utf8',HERE/'trim_worker.py',entry,lrat,core],folder/'trim.log',1800,6144)
            if rc:raise RuntimeError('Core trimming failed/timed out: '+str(entry))
            paths += [core,folder/'trim.log']
        artifacts={str(p.relative_to(ROOT)):sha(p) for p in paths}
        save(cache,dict(status='VERIFIED_TRIMMED_NOT_LEAN',identity=identity,artifacts=artifacts,finished=now()))
        with MUTEX:STATE['stages'][str(entry)]['native']='VERIFIED';publish()

def extra_evidence():
    """Regenerate missing evidence even for entries whose Lean proof uses a region cover."""
    for key,row in SURVEY['entries'].items():
        entry=int(key)
        if entry in COVER['representatives'] or row['certificate_present']:continue
        failure_key='evidence-'+key
        if failure_key in STATE['failures']:continue
        try:evidence(entry,False)
        except Exception:
            with MUTEX:STATE['failures'][failure_key]=dict(error=traceback.format_exc(),time=now())
        finally:
            with MUTEX:STATE['active'].pop(key,None);publish()

def geometry(entry,data_only=False):
    cmd=[sys.executable,'-X','utf8',str(HERE/'generate_bank_bridge.py'),str(entry)]
    if data_only:cmd.append('--data-only')
    result=subprocess.run(cmd,cwd=ROOT,env=ENV,capture_output=True,text=True,encoding='utf-8',timeout=300)
    if result.returncode:raise RuntimeError(result.stdout+result.stderr)

def group(rep):
    try:
        evidence(rep)
        boolean=emit_boolean(rep);geometry(rep)
        core=read(OUT/f'cores/entry{rep:03d}.json');prefix=f'E96{rep:03d}'
        modules=boolean+[prefix+'Data',prefix+'Semantics']+[prefix+f'Clauses{i:02d}' for i in range((len(core['clauses'])+31)//32)]+[prefix+'Complete']
        for name in modules:check(name,rep)
        axes={t:audit(prefix+'Complete',f'Snake9.Regrowth96.{prefix}.'+t) for t in ['region_exclusion','no192','no_long_prefix','no_long_suffix']}
        with MUTEX:
            STATE['representatives'][str(rep)]=dict(status='PASSED',modules=modules,axioms=axes,finished=now())
            STATE['stages'][str(rep)]['lean']='PASSED';publish()
        for i,c in COVER['entries'].items():
            entry=int(i)
            if c['representative']!=rep:continue
            if entry!=rep:geometry(entry,True);check(f'E96{entry:03d}Data',rep)
            module=emit_cover(entry,rep,c['translation']);check(module,rep)
            axes=audit(module,f'Snake9.Regrowth96.Bank96.entry{entry}')
            with MUTEX:
                STATE['entries'][str(entry)]=dict(status='PASSED',module=module,representative=rep,translation=c['translation'],axioms=axes,finished=now())
                publish()
            print('AUDITED ENTRY',entry,flush=True)
        with MUTEX:STATE['failures'].pop(str(rep),None)
    except Exception:
        with MUTEX:STATE['failures'][str(rep)]=dict(error=traceback.format_exc(),time=now())
        print('FAILED',rep,traceback.format_exc(),flush=True)
    finally:
        with MUTEX:STATE['active'].pop(str(rep),None);publish()

def final_audit():
    for name,r in RECORDS.items():
        if r['status']!='PASSED' or sha(ROOT/r['source'])!=r['source_sha256'] or sha(object_path(name))!=r['artifact_sha256']:raise ValueError('Invalid module receipt '+name)
        if sha(ROOT/r['log'])!=r['log_sha256']:raise ValueError('Invalid log '+name)
        if any(sha(object_path(d))!=h for d,h in r['dependencies'].items()):raise ValueError('Changed dependency '+name)
    assert set(STATE['entries'])=={str(i) for i in range(262)}
    for i,r in STATE['entries'].items():audit(r['module'],'Snake9.Regrowth96.Bank96.entry'+i)
    for r in COVER['representatives']:
        receipt=read(OUT/f'cores/entry{r:03d}.receipt.json')
        for p,h in receipt['artifacts'].items():
            if sha(ROOT/p)!=h:raise ValueError('Certificate evidence changed')
    name=aggregate();check(name,'aggregate',True)
    axes={t:audit(name,'Snake9.Regrowth96.Bank96.'+t) for t in ['bank_no192','bank_no_long_prefix','bank_no_long_suffix','bank_end_segment_length_le191']}
    save(OUT/'final-audit.json',dict(status='PASSED',entries=262,axioms=axes,modules=len(RECORDS),finished=now()))

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--workers',type=int,default=3);ap.add_argument('--representatives',type=int,nargs='+');ap.add_argument('--retry-failures',action='store_true');args=ap.parse_args()
    guard=(OUT/'runner.lock').open('a+b');guard.seek(0);guard.write(b'0');guard.flush();guard.seek(0)
    try:msvcrt.locking(guard.fileno(),msvcrt.LK_NBLCK,1)
    except OSError:raise SystemExit('Runner already active; no duplicate started')
    # Do not display previous completion counts until their saved identities pass.
    valid=True
    for name,r in RECORDS.items():
        if r['status']!='PASSED':continue
        try:
            if r['status']!='PASSED' or sha(ROOT/r['source'])!=r['source_sha256'] or sha(object_path(name))!=r['artifact_sha256'] or sha(ROOT/r['log'])!=r['log_sha256'] or r['compiler_sha256']!=sha(LEAN):valid=False;break
            if any(sha(object_path(d))!=h for d,h in r['dependencies'].items()):valid=False;break
        except (OSError,KeyError):valid=False;break
    if not valid:STATE['entries']={};STATE['representatives']={}
    STATE.pop('finished',None)
    STATE.update(status='RUNNING',active={},started=now(),pid=os.getpid(),workers=args.workers,process_created=psutil.Process().create_time());publish()
    try:
        setup()
        STATE['failures'].pop('setup',None)
        reps=args.representatives or COVER['representatives']
        # An unchanged failed group is never retried automatically.
        reps=[r for r in reps if args.retry_failures or str(r) not in STATE['failures']]
        with concurrent.futures.ThreadPoolExecutor(max_workers=args.workers) as pool:
            jobs=[pool.submit(group,r) for r in reps]
            if not args.representatives:jobs.append(pool.submit(extra_evidence))
            for job in jobs:job.result()
        if len(STATE['entries'])==262 and not STATE['failures']:
            final_audit();STATE['status']='VERIFIED_AWAITING_PACKAGING'
        else:STATE['status']='NEEDS_REPAIR' if STATE['failures'] else 'STOPPED_CHECKPOINTED'
    except Exception:
        STATE['status']='NEEDS_REPAIR';STATE['failures']['setup']=dict(error=traceback.format_exc(),time=now());print(traceback.format_exc(),flush=True)
    finally:
        STATE['active']={};STATE['finished']=now();publish();guard.close()

if __name__=='__main__':main()
