"""One bounded prefix-transport worker, after159 stops; no Lean or solver."""
from pathlib import Path
import argparse
import hashlib
import json
import os
import re
import subprocess
import sys
import time
from native_guard import snapshot

H=Path(__file__).resolve().parents[1]; R=H.parents[1]
GIB=1024**3


def sha(path):
    h=hashlib.sha256()
    with Path(path).open('rb') as f:
        for b in iter(lambda:f.read(1048576),b''):h.update(b)
    return h.hexdigest()


def retry_permission(action):
    for attempt in range(40):
        try:
            return action()
        except PermissionError:
            if attempt == 39:
                raise
            time.sleep(.05)


def read(path):
    return retry_permission(lambda:json.loads(Path(path).read_text(encoding='utf-8-sig')))


def save(path,obj):
    tmp=path.with_suffix(path.suffix+'.tmp')
    tmp.write_text(json.dumps(obj,indent=2)+'\n',encoding='utf-8',newline='\n')
    retry_permission(lambda:tmp.replace(path))


def terminal159():
    folder=R/'milestones/159-share18-proof-continuation/data'
    if any((folder/name).exists() for name in ['semantic-batch.lock','semantic-final-batch.lock']):return None
    path=folder/'semantic-progress.json'
    if not path.exists():return None
    record=read(path)
    if record.get('active') is not None:return None
    if record.get('status') not in ['PASS_COMPLETE_SEMANTIC_MODULES','PASS_BOUNDED_SEMANTIC_PREFIX','STOPPED_ON_FAILED_OR_INCOMPLETE_MODULE']:
        return None
    final_path=folder/'semantic-final-progress.json'
    final=None
    if final_path.exists():
        final_record=read(final_path)
        if final_record.get('active') is not None:return None
        if final_record.get('status') not in ['PASS_COMPLETE_SEMANTIC_MODULES','PASS_BOUNDED_SEMANTIC_PREFIX','STOPPED_ON_FAILED_OR_INCOMPLETE_MODULE']:
            return None
        final=dict(path=final_path.relative_to(R).as_posix(),sha256=sha(final_path),status=final_record['status'])
    return dict(path=path.relative_to(R).as_posix(),sha256=sha(path),status=record['status'],final_progress=final)


def failure(resource,owned,start=False):
    if resource['errors']:return 'RESOURCE_QUERY_FAILED'
    if resource['lean_processes']:return 'LEAN_PROCESS_PRESENT'
    if resource['graph_processes']:return 'GRAPH_PROCESS_PRESENT'
    if resource['free_bytes'] < (1536*1024**2 if start else 768*1024**2):return 'LOW_FREE_MEMORY'
    if sum(x['private_bytes'] for x in resource['owned_memory']) > GIB:return 'OWNED_PRIVATE_MEMORY_OVER_1_GIB'
    if not any(x['pid']==os.getpid() for x in resource['owned_memory']):return 'OWNED_MEMORY_QUERY_MISSING'
    return None


def main():
    assert __debug__
    ap=argparse.ArgumentParser();ap.add_argument('--label',default='prefix1055');a=ap.parse_args()
    assert re.fullmatch('[A-Za-z0-9_-]+',a.label)
    planpath=H/'data/source-plan.json';plan=read(planpath)
    assert plan['status']=='SOURCE_PREPARED_NOT_EXECUTED'
    for path,digest in {**plan['source_pins'],**plan['input_pins']}.items():assert sha(R/path)==digest,path
    terminal=terminal159()
    if terminal is None:
        print(json.dumps(dict(status='NOT_STARTED_WAITING_FOR159_TERMINAL')));return 2
    owned={os.getpid()};initial=snapshot(owned);reason=failure(initial,owned,True)
    if reason:
        print(json.dumps(dict(status='NOT_STARTED_RESOURCE_GATE',reason=reason,resources=initial)));return 2
    run=H/'data'/a.label;assert not run.exists(),'Preserve earlier run; choose another label'
    lock=H/'data/prefix-transport.lock';identity=dict(parent_pid=os.getpid(),run=str(run))
    try:
        with lock.open('x',encoding='utf-8') as f:json.dump(identity,f)
    except FileExistsError:
        print(json.dumps(dict(status='NOT_STARTED_EXISTING_TRANSPORT_LOCK')));return 2
    worker=None;record=dict(status='PREPARING',parent_pid=os.getpid(),source_plan_sha256=sha(planpath),
        terminal159=terminal,initial_resources=initial,peak_owned_private_bytes=0,stop_reason=None,
        memory_limit_bytes=GIB,timeout_seconds=180,Lean_invoked=False,solver_invoked=False)
    try:
        run.mkdir()
        save(run/'request.json',dict(parent_pid=os.getpid(),source_plan_sha256=sha(planpath),
            terminal159_progress_sha256=terminal['sha256'],
            terminal159_final_progress=terminal['final_progress'],input_pins=plan['input_pins']))
        env=os.environ.copy();env['SNAKE160_PARENT']=str(os.getpid())
        command=[sys.executable,'-B','-X','utf8',str(H/'scripts/prefix_transport.py'),'--run',str(run),'--parent',str(os.getpid())]
        started=time.monotonic()
        with (run/'stdout.log').open('w',encoding='utf-8') as out,(run/'stderr.log').open('w',encoding='utf-8') as err:
            worker=subprocess.Popen(command,cwd=R,env=env,stdout=out,stderr=err)
            owned.add(worker.pid);record.update(status='RUNNING',worker_pid=worker.pid,command=command)
            while worker.poll() is None:
                resources=snapshot(owned);reason=failure(resources,owned)
                record['last_resources']=resources
                record['peak_owned_private_bytes']=max(record['peak_owned_private_bytes'],sum(x['private_bytes'] for x in resources['owned_memory']))
                if terminal159()!=terminal:reason=reason or '159_STATE_CHANGED'
                if time.monotonic()-started>180:reason=reason or 'TIME_LIMIT'
                if reason:
                    record.update(status='STOPPED',stop_reason=reason)
                    worker.terminate();worker.wait(timeout=15);break
                save(run/'run-status.json',record);time.sleep(.2)
        record['exit_code']=worker.wait(timeout=15)
        if record['stop_reason'] is None:
            if record['exit_code']:
                record.update(status='FAILED',stop_reason='WORKER_EXIT')
            else:
                result=read(run/'prefix-transport.json')
                assert result['status']=='PASS_EXACT_ACCEPTED_PREFIX_TRANSPORT_CHECKPOINT_SOURCE_ONLY'
                assert not result['Lean_checkpoint_checked'] and not result['new_global_bound']
                record.update(status=result['status'],receipt_sha256=sha(run/'prefix-transport.json'))
    except BaseException as error:
        record.update(status='FAILED',error=repr(error))
        if worker is not None and worker.poll() is None:worker.terminate();worker.wait(timeout=15)
        raise
    finally:
        if run.exists():save(run/'run-status.json',record)
        if lock.exists() and read(lock)==identity:lock.unlink()
    print(json.dumps({k:record.get(k) for k in ['status','stop_reason','exit_code','peak_owned_private_bytes']}))
    return 0 if record['status'].startswith('PASS_') else 2


if __name__=='__main__':raise SystemExit(main())
