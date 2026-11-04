"""Run one compiler at a time and retain every bounded replay batch record."""
from pathlib import Path
import argparse
import hashlib
import json
import os
import subprocess
import sys
import time

H = Path(__file__).resolve().parents[1]
R = H.parents[1]

def read(p):
    for attempt in range(40):
        try:
            return json.loads(p.read_text(encoding='utf-8-sig'))
        except PermissionError:
            if attempt == 39:
                raise
            time.sleep(0.05)

def atomic(p, value):
    tmp = p.with_name(p.name + '.' + str(os.getpid()) + '.tmp')
    b = json.dumps(value, indent=2) + '\n'
    for attempt in range(40):
        try:
            tmp.write_text(b, encoding='utf-8')
            os.replace(tmp, p)
            return
        except PermissionError:
            if attempt == 39:
                raise
            time.sleep(0.05)

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--pilot', action='store_true')
    ap.add_argument('--limit', type=int)
    args = ap.parse_args()
    plan = read(H / 'data/kernel-execution.json')
    assert hashlib.sha256(Path(__file__).read_bytes()).hexdigest() == plan['driver_sha256']
    if not args.pilot:
        pilot = read(H / 'data/pilot-completion.json')
        assert pilot['status'] == 'PASS_FIRST32_REMAINING_SEGMENTS'
        assert pilot['execution_plan_sha256'] == hashlib.sha256((H / 'data/kernel-execution.json').read_bytes()).hexdigest()
    modules = plan['pilot_module_order'] if args.pilot else plan['new_module_order']
    lock = H / 'data/replay-batch.lock'
    with lock.open('x') as f:
        json.dump({'pid': os.getpid()}, f)
    state = dict(status='RUNNING', pid=os.getpid(), checked=[], active=None,
                 new_modules=0, total_modules=len(modules), pilot=args.pilot)
    folder = H / 'logs'
    folder.mkdir(parents=True, exist_ok=True)
    record = folder / ('replay-batch-' + str(time.time_ns()) + '.json')

    def save():
        atomic(record, state)
        atomic(H / 'data/replay-progress.json', state)

    try:
        save()
        for module in modules:
            existed = (H / 'data' / (module + '-audit.json')).exists()
            if not existed and args.limit is not None and state['new_modules'] >= args.limit:
                state['status'] = 'PASS_BOUNDED_REPLAY_PREFIX'
                break
            with (folder / (record.stem + '-' + module + '.log')).open('w', encoding='utf-8') as log:
                child = subprocess.Popen([sys.executable, '-B', '-X', 'utf8',
                                          str(H / 'scripts/check_replay.py'), module],
                                         cwd=R, stdout=log, stderr=subprocess.STDOUT)
                state['active'] = {'module': module, 'pid': child.pid}
                save()
                code = child.wait()
            state['active'] = None
            if code:
                state.update(status='STOPPED_ON_FAILED_OR_INCOMPLETE_MODULE', failed_module=module)
                save()
                raise SystemExit(code)
            state['checked'].append(module)
            state['new_modules'] += int(not existed)
            save()
            print('CHECKED', len(state['checked']), module, flush=True)
        else:
            state['status'] = 'PASS_PILOT_MODULES' if args.pilot else 'PASS_COMPLETE_REPLAY_MODULES'
    finally:
        save()
        lock.unlink()
        print(state['status'], flush=True)

if __name__ == '__main__':
    main()
