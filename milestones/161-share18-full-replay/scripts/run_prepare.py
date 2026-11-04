"""Guard the161 transport/export worker. Never invokes Lean or a solver."""
import argparse
import json
import os
import re
import subprocess
import sys
import time
from common import H,R,read,sha,save,check_pins,completed160,no_batch_locks
from native_guard import snapshot


def failure(resource,owned,start=False):
    if resource['errors']:return 'RESOURCE_QUERY_FAILED'
    if resource['lean_processes']:return 'LEAN_PROCESS_PRESENT'
    if resource['graph_processes']:return 'GRAPH_PROCESS_PRESENT'
    if resource['free_bytes']<(1536*1024**2 if start else 768*1024**2):return 'LOW_FREE_MEMORY'
    if sum(row['private_bytes'] for row in resource['owned_memory'])>1024**3:return 'OWNED_MEMORY_OVER_1_GIB'
    if not any(row['pid']==os.getpid() for row in resource['owned_memory']):return 'OWNED_MEMORY_QUERY_MISSING'
    if not no_batch_locks():return '159_OR160_BATCH_PRESENT'
    return None


def main():
    assert __debug__
    ap=argparse.ArgumentParser();ap.add_argument('--label',default='remaining-v1');args=ap.parse_args()
    assert re.fullmatch('[A-Za-z0-9_-]+',args.label)
    plan=read(H/'data/preparation.json');assert plan['status']=='SOURCE_PREPARED_NOT_EXECUTED'
    check_pins(plan);completed160()
    assert not (H/'data/full-source-plan.json').exists(),'Existing source plan must remain immutable'
    owned={os.getpid()};initial=snapshot(owned);reason=failure(initial,owned,True)
    if reason:
        print(json.dumps(dict(status='NOT_STARTED_RESOURCE_GATE',reason=reason,resources=initial)));return 2
    run=H/'data'/args.label;assert not run.exists(),'Choose a fresh label'
    lock=H/'data/preparation-worker.lock';identity=dict(parent_pid=os.getpid(),run=str(run))
    try:
        with lock.open('x',encoding='utf-8') as f:json.dump(identity,f)
    except FileExistsError:
        print(json.dumps(dict(status='NOT_STARTED_EXISTING_TRANSPORT_LOCK')));return 2
    worker=None;record=dict(status='PREPARING',parent_pid=os.getpid(),initial_resources=initial,
        preparation_sha256=sha(H/'data/preparation.json'),stop_reason=None,peak_owned_private_bytes=0,
        memory_limit_bytes=1024**3,time_limit_seconds=600,Lean_invoked=False,solver_invoked=False)
    try:
        run.mkdir();save(run/'request.json',dict(parent_pid=os.getpid(),preparation_sha256=record['preparation_sha256']))
        env=os.environ.copy();env['SNAKE161_PARENT']=str(os.getpid())
        command=[sys.executable,'-B','-X','utf8',str(H/'scripts/transport_remaining.py'),'--run',str(run),'--parent',str(os.getpid())]
        started=time.monotonic()
        with (run/'stdout.log').open('w',encoding='utf-8') as out,(run/'stderr.log').open('w',encoding='utf-8') as err:
            worker=subprocess.Popen(command,cwd=R,env=env,stdout=out,stderr=err);owned.add(worker.pid)
            record.update(status='RUNNING',worker_pid=worker.pid,command=command)
            while worker.poll() is None:
                resource=snapshot(owned);reason=failure(resource,owned)
                record['last_resources']=resource
                record['peak_owned_private_bytes']=max(record['peak_owned_private_bytes'],sum(row['private_bytes'] for row in resource['owned_memory']))
                if time.monotonic()-started>600:reason=reason or 'TIME_LIMIT'
                if reason:
                    record.update(status='STOPPED',stop_reason=reason);worker.terminate();worker.wait(timeout=15);break
                save(run/'run-status.json',record);time.sleep(.2)
        record['exit_code']=worker.wait(timeout=15)
        if record['stop_reason'] is None:
            if record['exit_code']:record.update(status='FAILED',stop_reason='WORKER_EXIT')
            else:
                sources=read(H/'data/full-source-plan.json')
                assert sources['status']=='SOURCE_PREPARED_UNCHECKED' and not sources['Lean_invoked']
                check_pins(plan);completed160()
                record.update(status='PASS_REMAINING_TRANSPORT_AND_UNCHECKED_SOURCES',
                    transport_sha256=sha(run/'transport.json'),full_source_plan_sha256=sha(H/'data/full-source-plan.json'))
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
