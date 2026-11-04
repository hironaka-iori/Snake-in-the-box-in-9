"""Run one resource-gated conditional graph experiment after156 completion."""
from pathlib import Path
import argparse
import hashlib
import json
import os
import re
import subprocess
import sys
import time
from datetime import datetime, timezone
from native_guard import snapshot

H = Path(__file__).resolve().parents[1]
R = H.parents[1]
GIB = 1024**3


def sha(path):
    value = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for block in iter(lambda: stream.read(1048576), b''):
            value.update(block)
    return value.hexdigest()


def read(path):
    return json.loads(Path(path).read_text(encoding='utf-8-sig'))


def save(path, value):
    temporary = path.with_suffix(path.suffix+'.tmp')
    temporary.write_text(json.dumps(value, indent=2)+'\n', encoding='utf-8', newline='\n')
    temporary.replace(path)


def resource_failure(value, owned, before_start=False):
    if value['errors']:
        return 'RESOURCE_QUERY_FAILED'
    if value['lean_processes']:
        return 'LEAN_PROCESS_PRESENT'
    if any(row['pid'] not in owned for row in value['graph_processes']):
        return 'OTHER_GRAPH_PROCESS_PRESENT'
    if value['free_bytes'] < (2*GIB if before_start else 768*1024**2):
        return 'LOW_FREE_MEMORY'
    if sum(row['private_bytes'] for row in value['owned_memory']) > GIB:
        return 'OWNED_MEMORY_LIMIT'
    return None


def main():
    assert __debug__, 'Run Python without -O'
    parser = argparse.ArgumentParser()
    parser.add_argument('--label', default='floor17-range496')
    args = parser.parse_args()
    assert re.fullmatch(r'[A-Za-z0-9_-]+', args.label)
    prep_path = H / 'data/preparation.json'
    prep = read(prep_path)
    assert prep['status'] == 'SOURCE_PREPARED_NOT_EXECUTED'
    assert sha(R / prep['plan_path']) == prep['plan_sha256']
    for relative, digest in {**prep['script_pins'], **prep['input_pins']}.items():
        assert sha(R / relative) == digest, relative
    complete_path = R / 'milestones/155-share17-replay/data/actual-snake-completion.json'
    recovery_path = R / 'milestones/155-share17-replay/data/post-replay-recovery.json'
    if not complete_path.exists() or not recovery_path.exists():
        print(json.dumps(dict(status='NOT_STARTED_WAITING_FOR155_COMPLETION')))
        return 2
    complete = read(complete_path)
    recovery = read(recovery_path)
    assert recovery['status'] == 'PASS_DIRECT_FINAL_CHECKS_AFTER_PROCESS_QUERY_ERROR'
    assert recovery['full_replay_modules'] == 137 and recovery['full_driver_exit_code'] == 0
    assert recovery['final_composition_checked'] and recovery['actual_snake_audit_passed']
    assert recovery['original_failure_records_preserved'] and not recovery['new_global_upper_bound']
    # Historical STOPPED progress remains evidence, not a failed completion gate.
    for relative, digest in recovery['source_files_sha256'].items():
        assert sha(R / relative) == digest, relative
    assert complete['status'] == 'PASS_ACTUAL_SNAKE_SHARE17_WITH_COUNT_CONDITIONS'
    assert complete['bounds'] == [[4,4],[0,4],[4,4],[0,5],[3,3]]
    assert complete['reverse_bounds'] == [[3,3],[0,5],[4,4],[0,4],[4,4]]
    assert complete['count_conditions_retained'] and complete['reversal_included']
    assert not complete['extra_unsat_premise'] and not complete['new_global_upper_bound']
    auditor = R / 'milestones/155-share17-replay/scripts/audit_actual.py'
    for relative, digest in complete['source_files_sha256'].items():
        assert sha(R / relative) == digest, relative
    verification = subprocess.run([sys.executable, '-B', '-X', 'utf8', str(auditor), '--verify-only'],
        cwd=R, capture_output=True, text=True, encoding='utf-8', timeout=120)
    assert verification.returncode == 0, verification.stdout+verification.stderr
    assert json.loads(verification.stdout) == complete

    # The accepted156 receipt and its exact evidence closure must be unchanged.
    completion156_path = R / 'milestones/156-potential-range-and-paper/data/completion.json'
    completion156 = read(completion156_path)
    assert completion156['status'] == 'PASS_SCOPED_JOINT_OPTIMUM_AND_PAPER156'
    assert completion156['fixed_mean_range'] == 602
    assert completion156['equality_parameters'] == {'mean':496,'occurrence_credit':0,'range':602}
    assert not completion156['new_global_bound'] and completion156['unresolved_snake_premises']
    assert not completion156['complete_Lean_graph_certificate']
    oldhome = completion156_path.parent.parent
    for relative, digest in completion156['evidence_sha256'].items():
        assert sha(oldhome / relative) == digest, relative
    for relative, digest in prep['accepted156_pins'].items():
        assert sha(R / relative) == digest, relative
    oldresult = read(oldhome / 'data/share17-range496/result.json')
    oldrun = read(oldhome / 'data/share17-range496/run-status.json')
    assert oldresult['status'] == oldrun['status'] == 'PASS_MINIMUM_RANGE_AT_MEAN496'
    assert oldresult['potential_range'] == oldresult['certified_range_lower_bound'] == 602
    assert oldresult['all_edge_inequalities_checked'] == 4661572
    assert oldresult['minimum_slack'] == 0
    owned = {os.getpid()}
    initial = snapshot(owned)
    failure = resource_failure(initial, owned, before_start=True)
    if failure:
        print(json.dumps(dict(status='NOT_STARTED_RESOURCE_GATE', reason=failure, resources=initial)))
        return 2
    legacy_locks = list((R / 'milestones').glob('*/data/fullgraph.lock'))
    if legacy_locks:
        print(json.dumps(dict(status='NOT_STARTED_LEGACY_GRAPH_LOCK',
                              locks=[str(path) for path in legacy_locks])))
        return 2
    run = H / 'data' / args.label
    assert not run.exists(), 'Preserve earlier results; choose a new label'
    lock_path = R / 'work/fullgraph-active.lock'
    lock_value = dict(parent_pid=os.getpid(), run=str(run), preparation_sha256=sha(prep_path))
    try:
        with lock_path.open('x', encoding='utf-8') as stream:
            json.dump(lock_value, stream)
    except FileExistsError:
        print(json.dumps(dict(status='NOT_STARTED_GRAPH_LOCK_EXISTS', lock=str(lock_path))))
        return 2
    worker = None
    record = dict(status='PREPARING', started_utc=datetime.now(timezone.utc).isoformat(),
        parent_pid=os.getpid(), preparation_sha256=sha(prep_path), initial_resources=initial,
        discovery_seconds_limit=600, total_seconds_limit=900, stop_reason=None,
        peak_owned_private_bytes=0, new_global_bound=False)
    try:
        run.mkdir()
        completion_pins = dict(prep['accepted156_pins'])
        for relative, digest in complete['source_files_sha256'].items():
            assert relative not in completion_pins or completion_pins[relative] == digest
            completion_pins[relative] = digest
        for relative, digest in recovery['source_files_sha256'].items():
            assert relative not in completion_pins or completion_pins[relative] == digest
            completion_pins[relative] = digest
        completion_pins[complete_path.relative_to(R).as_posix()] = sha(complete_path)
        completion_pins[recovery_path.relative_to(R).as_posix()] = sha(recovery_path)
        save(run / 'request.json', dict(parent_pid=os.getpid(), preparation_sha256=sha(prep_path),
             completion_pins=completion_pins, floor_profile='012034-floor17-other-floors-unchanged-plus-suffix17',
             mean=496, occurrence_credit=0, new_global_bound=False))
        save(run / 'run-status.json', record)
        environment = os.environ.copy()
        environment['SNAKE158_WORKER_PARENT'] = str(os.getpid())
        command = [sys.executable, '-B', '-X', 'utf8', str(H / 'scripts/potential_range.py'),
                   '--run', str(run), '--parent', str(os.getpid())]
        started = time.monotonic()
        with (run / 'stdout.log').open('w', encoding='utf-8') as stdout, \
             (run / 'stderr.log').open('w', encoding='utf-8') as stderr:
            worker = subprocess.Popen(command, cwd=R, env=environment, stdout=stdout, stderr=stderr)
            owned.add(worker.pid)
            record.update(status='RUNNING', worker_pid=worker.pid, command=command)
            save(run / 'run-status.json', record)
            while worker.poll() is None:
                resources = snapshot(owned)
                failure = resource_failure(resources, owned)
                private = sum(row['private_bytes'] for row in resources['owned_memory'])
                record['peak_owned_private_bytes'] = max(record['peak_owned_private_bytes'], private)
                record['last_resources'] = resources
                progress_path = run / 'progress.json'
                progress = read(progress_path) if progress_path.exists() else {}
                if time.monotonic()-started >= 900:
                    failure = failure or 'TOTAL_TIME_LIMIT'
                if progress.get('phase') == 'DISCOVERY' and time.monotonic()-progress['discovery_started'] >= 600:
                    failure = failure or 'DISCOVERY_TIME_LIMIT'
                record['progress'] = progress
                if failure:
                    record.update(status='STOPPED', stop_reason=failure)
                    worker.terminate(); worker.wait(timeout=15)
                    break
                save(run / 'run-status.json', record)
                time.sleep(1)
        code = worker.wait(timeout=15)
        record['exit_code'] = code
        if record['stop_reason'] is None:
            if code != 0:
                record.update(status='FAILED', stop_reason='WORKER_EXIT')
            else:
                result = read(run / 'result.json')
                assert result['new_global_bound'] is False
                record.update(status=result['status'], result_sha256=sha(run / 'result.json'))
    except BaseException as error:
        record.update(status='FAILED', error=repr(error))
        if worker is not None and worker.poll() is None:
            worker.terminate(); worker.wait(timeout=15)
        raise
    finally:
        record['finished_utc'] = datetime.now(timezone.utc).isoformat()
        if run.exists():
            save(run / 'run-status.json', record)
        if lock_path.exists() and read(lock_path) == lock_value:
            lock_path.unlink()
    print(json.dumps({key:record.get(key) for key in ['status','stop_reason','exit_code',
        'peak_owned_private_bytes','new_global_bound']}))
    return 0 if record['status'].startswith('PASS_') else 2


if __name__ == '__main__':
    raise SystemExit(main())
