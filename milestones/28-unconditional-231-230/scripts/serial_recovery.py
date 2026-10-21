"""Wait for live checks, then resume failed jobs one at a time from checkpoints.

This queue never kills a process or changes memory/page-file settings. It was
introduced after observed Windows 1455 and supervisor MemoryError failures.
"""
import argparse
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import time
import runner as r

JOB = r.HERE / 'runtime/serial-recovery'


def run(wait_pids):
    import msvcrt
    JOB.mkdir(parents=True, exist_ok=True)
    held = (JOB / 'worker.lock').open('a+b')
    held.seek(0); held.write(b'0'); held.flush(); held.seek(0)
    msvcrt.locking(held.fileno(), msvcrt.LK_NBLCK, 1)
    previous = r.read(JOB / 'state.json') if (JOB / 'state.json').exists() else None
    if previous:
        r.atomic(JOB / 'history' / f'{time.time_ns()}.json', previous)
    state = dict(status='waiting_existing', pid=os.getpid(), started=r.now(), waiting=[], jobs=[],
                 script_sha256=r.digest(__file__), source_commit=r.git('rev-parse','HEAD').decode().strip(),
                 scope='Serial operational recovery; no theorem completion asserted')
    for pid in wait_pids:
        try:
            proc = r.psutil.Process(pid); args = proc.cmdline()
            assert any('28-unconditional-231-230' in x for x in args), ('Unrelated PID',pid,args)
            state['waiting'].append(dict(pid=pid, created=proc.create_time(), command=args))
        except r.psutil.NoSuchProcess:
            pass
    scripts = r.HERE / 'scripts'
    count_targets = ['FastCountD012A11.LocalWindow', 'FastCountD012A12.LocalWindow',
                     'FastCountD012A13.LocalWindow', 'FastCountQ012A14.LocalWindow']
    jobs = [
        ('count-pairs', [str(scripts/'develop_lean.py'), *count_targets, '--source-root',
                         'milestones/28-unconditional-231-230/runtime/count-pairs/src'],
         r.HERE/'runtime/bridge-development/state.json', None),
        ('fast-share', [str(scripts/'fast_share_batch.py'), 'run'], r.HERE/'runtime/fast-kernel/state.json', 'boolean_complete'),
        ('applicability', [str(scripts/'applicability_batch.py'), 'run'], r.HERE/'runtime/applicability/state.json', 'applicability_complete'),
        ('count-tables', [str(scripts/'count_table_batch.py'), 'run'], r.HERE/'runtime/count-tables/state.json', 'coverage_complete')]
    state['controller_sha256'] = {str(p): r.digest(p) for p in
        [scripts/'serial_recovery.py', scripts/'runner.py', scripts/'replay.py',
         scripts/'develop_lean.py', scripts/'fast_share_batch.py',
         scripts/'applicability_batch.py', scripts/'count_table_batch.py']}
    print(json.dumps(dict(pid=os.getpid(), status=state['status'], wait_pids=[x['pid'] for x in state['waiting']])), flush=True)
    try:
        while True:
            active, unavailable = [], []
            for row in state['waiting']:
                try:
                    proc = r.psutil.Process(row['pid'])
                    if proc.create_time() == row['created'] and proc.is_running():
                        active.append(row['pid'])
                except r.psutil.NoSuchProcess:
                    pass
                except (OSError, r.psutil.Error) as error:
                    unavailable.append(dict(pid=row['pid'], error=str(error)))
            state.update(active_wait_pids=active, observation_errors=unavailable, heartbeat=r.now())
            r.atomic(JOB/'state.json', state)
            if not active and not unavailable:
                break
            time.sleep(10)
        for label, args, checkpoint, expected in jobs:
            for path, digest in state['controller_sha256'].items():
                assert r.digest(path) == digest, ('Controller changed while queued', path)
            archive = JOB/'history'/f'{time.time_ns()}-{label}'
            archive.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(checkpoint, archive/'state-before.json')
            prior = r.read(checkpoint)
            logs = [prior['latest_log']] if prior.get('latest_log') else []
            if label == 'count-pairs':
                logs.extend(str(checkpoint.parent/(name.replace('.', '_')+'.log')) for name in count_targets)
            for path in logs:
                source = Path(path)
                if source.exists():
                    shutil.copyfile(source, archive/source.name)
            command = [sys.executable, *args]
            log = JOB/(label+'.log')
            state.update(status='running', current=label, command=command, latest_log=str(log), heartbeat=r.now())
            r.atomic(JOB/'state.json', state)
            print(label, 'START', flush=True)
            start = time.monotonic()
            with log.open('w',encoding='utf-8') as output:
                output.write(json.dumps(command)+'\n'); output.flush()
                child = subprocess.Popen(command,cwd=r.ROOT,stdout=output,stderr=subprocess.STDOUT)
                state['child_pid'] = child.pid
                while child.poll() is None:
                    state['heartbeat'] = r.now(); r.atomic(JOB/'state.json',state); time.sleep(10)
            result = r.read(checkpoint)
            if expected is None:
                success = all(name in result.get('completed',{}) for name in count_targets)
            else:
                success = result.get('status') == expected
            state['jobs'].append(dict(name=label, returncode=child.returncode, status=result.get('status'),
                                       success=success, elapsed_seconds=time.monotonic()-start,
                                       checkpoint=str(checkpoint), log_sha256=r.digest(log)))
            r.atomic(JOB/'state.json',state)
            if child.returncode or not success:
                raise RuntimeError(f'{label} needs investigation; queue stopped without starting later jobs')
        state.update(status='queue_complete', current=None, finished=r.now())
    except BaseException as error:
        state.update(status='action_required', failure=str(error), heartbeat=r.now())
        raise
    finally:
        r.atomic(JOB/'state.json',state); held.close()


if __name__ == '__main__':
    parser = argparse.ArgumentParser(); parser.add_argument('--wait-pids',type=int,nargs='*',default=[])
    run(parser.parse_args().wait_pids)
