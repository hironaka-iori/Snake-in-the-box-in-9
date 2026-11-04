"""Resume the accepted prefix once resources recover; never lower proof gates."""
from pathlib import Path
import datetime, hashlib, json, os, subprocess, sys, time
from native_resources import snapshot

H=Path(__file__).resolve().parents[1];R=H.parents[1]
read=lambda p:json.loads(Path(p).read_text(encoding='utf-8-sig'))
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
lock=H/'data/memory-resume.lock';target=H/'data/memory-resume-progress.json'
assert not lock.exists() and not target.exists(), 'Inspect existing resource recovery first'
old=read(H/'data/full-replay-progress.json')
assert old['status']=='STOPPED_ON_FAILED_OR_INCOMPLETE_MODULE' and len(old['checked_modules'])==68
assert old['exception']=="AssertionError(('ReplayCheck153_00080', 1))"
assert not (H/'data/full-replay-batch.lock').exists()
assert read(H/'data/final-continuation-progress.json')['status']=='FAILED_REQUIRES_INSPECTION'
assert not (H/'data/final-continuation.lock').exists()
assert not (H/'data/ShareComplete155-audit.json').exists()
assert not (H/'data/ReplayCheck153_00080-audit.json').exists()
log=H/'logs/full-replay-launch-1793767660170134800-ReplayCheck153_00080.log'
output=log.read_text(encoding='utf-8')
assert 'pre_gate=resources()' in output and "'processes': []" in output
assert "'free_bytes': 1578532864" in output
assert sha(H/'scripts/run_full_replay.py')==old['driver_sha256']
assert sha(H/'scripts/check_full_replay.py')==old['checker_sha256']
assert sha(H/'data/full-source-plan.json')==old['plan_sha256']
original_plan=read(H/'data/final-composition-plan.json')
for p,d in original_plan['script_pins'].items():assert sha(R/p)==d,p
receipts={}
for row in old['checked_modules']:
    path=H/'data'/(row['module']+'-audit.json')
    assert sha(path)==row['receipt_sha256'];receipts[str(path)]=sha(path)
    q=read(path);assert q['status']=='PASS' and q['exit_code']==0 and q['stop_reason'] is None
    for p,d in q['dependencies'].items():assert sha(p)==d,p
    assert sha(q['source'])==q['source_sha256'] and sha(q['object'])==q['olean_sha256']
archive=H/'audit/memory-stop-68';archive.mkdir(parents=True,exist_ok=False)
archived={}
for name in ['full-replay-progress.json','final-composition-plan.json','final-continuation-progress.json']:
    src=H/'data'/name;dst=archive/name;dst.write_bytes(src.read_bytes());assert sha(src)==sha(dst)
    archived[name]=sha(dst)
(archive/'module80-preflight.log').write_bytes(log.read_bytes())
state=dict(status='WAITING_FOR_AVAILABLE_MEMORY',pid=os.getpid(),
    started_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
    accepted_modules=68,receipt_pins=receipts,archived_records=archived,
    waiting_free_bytes=int(2.5*1024**3),stable_seconds=10,
    previous_failure='Module80 rejected before compiler launch at1,578,532,864 free bytes.',
    thresholds_unchanged=True,stages=[],resource_samples=[])
def save():
    tmp=target.with_suffix('.pending');tmp.write_text(json.dumps(state,indent=2)+'\n',encoding='utf-8',newline='\n');os.replace(tmp,target)
with lock.open('x') as out:json.dump(dict(pid=os.getpid()),out)
save();full=None;continuation=None
try:
    since=None
    while True:
        current=snapshot();state['resource_samples'].append(current)
        state['resource_samples']=state['resource_samples'][-60:]
        ready=not current['errors'] and not current['processes'] and current['free_bytes']>=state['waiting_free_bytes']
        since=(since if since is not None else time.monotonic()) if ready else None
        state['last_sample_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat();save()
        if since is not None and time.monotonic()-since>=10:break
        time.sleep(2)
    for p,d in receipts.items():assert sha(p)==d,p
    assert sha(H/'data/full-replay-progress.json')==archived['full-replay-progress.json']
    for name in ['final-composition-plan.json','final-continuation-progress.json']:
        path=H/'data'/name;assert sha(path)==archived[name]
        # Exact historical bytes are preserved above; no accepted theorem uses this pending plan.
        path.unlink()
    stamp=str(time.time_ns());full_log=H/'logs'/('resource-resume-full-'+stamp+'.log')
    with full_log.open('w',encoding='utf-8') as out:
        full=subprocess.Popen([sys.executable,'-B','-X','utf8',str(H/'scripts/run_full_replay.py')],cwd=R,stdout=out,stderr=subprocess.STDOUT)
    state.update(status='RESUMED_FULL_REPLAY',full_pid=full.pid,full_log=str(full_log));save()
    ready=False
    for _ in range(100):
        if full.poll() is not None:raise AssertionError(('Full driver exited before preparation',full.returncode))
        try:
            progress=read(H/'data/full-replay-progress.json')
            ready=progress['status']=='RUNNING' and progress['pid']==full.pid
        except (OSError,json.JSONDecodeError):pass
        if ready:break
        time.sleep(.2)
    assert ready
    prep_log=H/'logs'/('resource-resume-final-preparation-'+stamp+'.log')
    with prep_log.open('w',encoding='utf-8') as out:
        result=subprocess.run([sys.executable,'-B','-X','utf8',str(H/'scripts/prepare_final_check.py')],cwd=R,stdout=out,stderr=subprocess.STDOUT)
    assert result.returncode==0,prep_log
    continuation_log=H/'logs'/('resource-resume-continuation-'+stamp+'.log')
    with continuation_log.open('w',encoding='utf-8') as out:
        continuation=subprocess.Popen([sys.executable,'-B','-X','utf8',str(H/'scripts/continue_after_full.py')],cwd=R,stdout=out,stderr=subprocess.STDOUT)
    state.update(continuation_pid=continuation.pid,continuation_log=str(continuation_log),
        final_plan_sha256=sha(H/'data/final-composition-plan.json'));save()
    code=full.wait();state['full_exit_code']=code;save()
    code2=continuation.wait();state['continuation_exit_code']=code2;save()
    assert code==code2==0
    assert read(H/'data/actual-snake-completion.json')['status']=='PASS_ACTUAL_SNAKE_SHARE17_WITH_COUNT_CONDITIONS'
    state['status']='CHECKING_SHORT_RANGE_IMPLICATIONS';save()
    range_log=H/'logs'/('resource-resume-range-'+stamp+'.log')
    with range_log.open('w',encoding='utf-8') as out:
        result=subprocess.run([sys.executable,'-B','-X','utf8',str(H/'analysis/check_range.py')],cwd=R,stdout=out,stderr=subprocess.STDOUT)
    state['range_log']=str(range_log);state['range_exit_code']=result.returncode
    assert result.returncode==0,range_log
    state['status']='PASS_SHARE17_AND_RANGE_ARITHMETIC'
except BaseException as error:
    state.update(status='STOPPED_REQUIRES_INSPECTION',exception=repr(error))
    # Never terminate an already launched proof job merely because preparation failed.
    if full is not None:state['full_poll']=full.poll()
    if continuation is not None:state['continuation_poll']=continuation.poll()
    raise
finally:
    state['finished_at']=datetime.datetime.now(datetime.timezone.utc).isoformat();save();lock.unlink()
    print(json.dumps({k:state[k] for k in ['status','accepted_modules','finished_at']}),flush=True)
