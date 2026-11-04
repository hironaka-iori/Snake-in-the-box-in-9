"""Bounded native certificates for one exact critical-context share query.

The continuing151 Lean process is never stopped or modified. Solver and
replay workers have separate time and memory guards; all incomplete output
is retained. Successful native replay is not a Lean/actual-snake theorem.
"""
from pathlib import Path
import argparse,datetime,hashlib,importlib.util,json,os,subprocess,sys,time
H=Path(__file__).resolve().parents[1];R=H.parents[2]
EXE=Path('D:/Codex/2026-10-01/it-should-have-a-property-of/work/lean-research/lean-4.19.0-windows/bin/cadical.exe')
EXE_SHA='4fb5f4f94a3632c185ea763f7da627d40038cca38d9481952d00d04cc881c94f'
TRIM=R/'milestones/109-relaxed-graph-test/upstream/milestones/10-window-aggregate/scripts/gen_lean_core.py'
REPLAY=R/'milestones/144-countfree-share18/scripts/certify_base.py'
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
ap=argparse.ArgumentParser();ap.add_argument('--replay',choices=['critical17']);args=ap.parse_args()

def save(path,obj):
    tmp=path.with_suffix('.pending');tmp.write_text(json.dumps(obj,indent=2)+'\n',encoding='utf-8');os.replace(tmp,path)

def module(name,path):
    spec=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m

def resources(pid=0):
    cmd='$o=Get-CimInstance Win32_OperatingSystem;$p=@(Get-CimInstance Win32_Process | Where-Object {$_.ProcessId -eq '+str(pid)+'} | Select-Object ProcessId,Name,CommandLine,PrivatePageCount);@{free_bytes=[long]$o.FreePhysicalMemory*1024;processes=$p}|ConvertTo-Json -Depth 4 -Compress'
    return json.loads(subprocess.check_output(['powershell.exe','-NoProfile','-Command',cmd],text=True))

def guarded(command,folder,label,seconds,raw=None):
    out,err=folder/(label+'-stdout.txt'),folder/(label+'-stderr.txt')
    state=dict(status='RUNNING',command=command,timeout_seconds=seconds,memory_limit_bytes=1024**3,
        minimum_free_bytes=1536*1024**2,samples=[],started_at=datetime.datetime.now(datetime.timezone.utc).isoformat())
    record=folder/(label+'-run.json');assert not record.exists()
    state['resource_gate']=resources();assert state['resource_gate']['free_bytes']>=3*1024**3
    begin=time.monotonic();child=None;stop=None
    try:
        with out.open('xb') as so,err.open('xb') as se:
            child=subprocess.Popen(command,stdout=so,stderr=se,cwd=R,creationflags=getattr(subprocess,'CREATE_NO_WINDOW',0))
            state['pid']=child.pid;save(record,state)
            while child.poll() is None:
                if time.monotonic()-begin>seconds:stop='TIMEOUT'
                observation=resources(child.pid);observation['elapsed_seconds']=time.monotonic()-begin
                state['samples'].append(observation);save(record,state)
                if observation['free_bytes']<state['minimum_free_bytes']:stop='LOW_FREE_MEMORY'
                if any(int(p['PrivatePageCount'])>state['memory_limit_bytes'] for p in observation['processes']):stop='MEMORY_LIMIT'
                if raw is not None and raw.exists() and raw.stat().st_size>128*1024**2:stop='RAW_PROOF_SIZE_LIMIT'
                if stop:child.kill();break
                time.sleep(1)
            code=child.wait(timeout=15)
    except BaseException as e:
        state['exception']=repr(e)
        if child is not None and child.poll() is None:child.kill();child.wait(timeout=15)
        raise
    finally:
        state.update(status=stop or ('EXITED' if child is not None else 'FAILED_BEFORE_START'),
            exit_code=child.returncode if child else None,seconds=time.monotonic()-begin,
            stdout_sha256=sha(out) if out.exists() else None,stderr_sha256=sha(err) if err.exists() else None)
        save(record,state)
    return state

if args.replay:
    folder=H/'work'/args.replay
    native=read(folder/'solver-run.json');assert native['status']=='EXITED' and native['exit_code']==20
    assert b's UNSATISFIABLE' in (folder/'solver-stdout.txt').read_bytes()
    enc=read(folder/'encoding.json');assert sha(folder/'input.cnf')==enc['cnf_sha256']
    trim=module('trim150',TRIM);replay=module('replay150',REPLAY)
    nv,clauses=replay.formula(folder/'input.cnf')
    assert (nv,len(clauses))==(enc['variables'],enc['clauses'])
    nl,nh,ids=trim.trim_lrat(str(folder/'raw.lrat'),str(folder/'trimmed.lrat'),len(clauses))
    assert ids==sorted(set(ids)) and all(1<=x<=len(clauses) for x in ids)
    save(folder/'core-ids.json',ids)
    (folder/'core.cnf').write_bytes((f'p cnf {nv} {len(ids)}\n'+''.join(' '.join(map(str,clauses[x-1]))+' 0\n' for x in ids)).encode('ascii'))
    out=dict(status='TRIMMED_NATIVE_REPLAY_PENDING',deductions=nl,hints=nh,core_clauses=len(ids),
        actual_pair_clauses_used=sum(x>enc['base_clauses'] for x in ids),
        source_files_sha256={str(TRIM):sha(TRIM),str(REPLAY):sha(REPLAY)},
        core_sha256=sha(folder/'core.cnf'),core_ids_sha256=sha(folder/'core-ids.json'),
        trimmed_sha256=sha(folder/'trimmed.lrat'),raw_sha256=sha(folder/'raw.lrat'),
        independent_replay_hint_limit=12000000,
        scope='Finite input contradiction only; Lean clause interpretation, replay and actual-snake transfer are separate.')
    save(folder/'native-replay.json',out)
    if nh<=12000000:
        checked=replay.replay(folder/'trimmed.lrat',clauses,ids,nl,nh)
        assert checked['status']=='PASS_COMPLETE_NATIVE_RUP_REPLAY'
        out.update(status='PASS_COMPLETE_NATIVE_RUP_REPLAY',replay=checked);save(folder/'native-replay.json',out)
    else:
        out['status']='NATIVE_REPLAY_PENDING_HINT_LIMIT';save(folder/'native-replay.json',out)
    print(json.dumps(out),flush=True)
    sys.exit(0)

assert sha(EXE)==EXE_SHA
target=H/'data/native-queries.json';assert not target.exists()
state=dict(status='RUNNING',started_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
    pid=os.getpid(),queries=[],script_sha256=sha(Path(__file__)),solver_sha256=EXE_SHA,
    source_files_sha256={str(TRIM):sha(TRIM),str(REPLAY):sha(REPLAY)},
    scope='One bounded exact critical-context certificate experiment, with the existing151 Lean replay left running. No new local theorem or global bound.')
save(target,state)
try:
    for label in ['critical17']:
        folder=H/'work'/label;encoding=read(folder/'encoding.json')
        assert sha(folder/'input.cnf')==encoding['cnf_sha256']
        for p,d in encoding['source_files_sha256'].items():assert sha(R/p)==d,p
        (folder/'driver.exact.py').write_bytes(Path(__file__).read_bytes())
        (folder/'trimmer.exact.py').write_bytes(TRIM.read_bytes())
        (folder/'replay-source.exact.py').write_bytes(REPLAY.read_bytes())
        raw=folder/'raw.lrat'
        row=dict(label=label,status='RUNNING_SOLVER');state['queries'].append(row);save(target,state)
        run=guarded([str(EXE),'-q','--lrat','--no-binary','--seed=1',str(folder/'input.cnf'),str(raw)],folder,'solver',90,raw)
        row.update(solver=run,status=run['status'])
        if run['status']=='EXITED' and run['exit_code']==20 and b's UNSATISFIABLE' in (folder/'solver-stdout.txt').read_bytes():
            row['status']='NATIVE_UNSAT_REPLAY_PENDING';save(target,state)
            run=guarded([sys.executable,'-B','-X','utf8',str(Path(__file__).resolve()),'--replay',label],folder,'replay',90)
            row['replay_worker']=run
            if run['status']=='EXITED' and run['exit_code']==0:
                row['replay']=read(folder/'native-replay.json');row['status']=row['replay']['status']
            else:row['status']='NATIVE_REPLAY_INCOMPLETE'
        elif run['status']=='EXITED' and run['exit_code']==10:row['status']='SAT_ASSIGNMENT_NOT_YET_INDEPENDENTLY_INTERPRETED'
        row['files_sha256']={p.name:sha(p) for p in folder.iterdir() if p.is_file() and p.suffix!='.pending'}
        save(target,state);print(label,row['status'],flush=True)
    state['status']='BOUNDED_NATIVE_QUERIES_FINISHED'
except BaseException as e:
    state.update(status='STOPPED_ON_ERROR',exception=repr(e));raise
finally:
    state['finished_at']=datetime.datetime.now(datetime.timezone.utc).isoformat();save(target,state)
    print(state['status'],flush=True)
