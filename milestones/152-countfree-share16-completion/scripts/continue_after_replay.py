"""Wait for the already running replay, then audit and check its consequence."""
from pathlib import Path
import datetime, hashlib, json, os, subprocess, sys, time

H = Path(__file__).resolve().parents[1]
R = H.parents[1]
P = R/'milestones/151-countfree-replay-pilot'
read = lambda p: json.loads(p.read_text(encoding='utf-8-sig'))
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
receipt = H/'data/final-continuation-progress.json'
assert not receipt.exists()
pins = {str(H/'scripts'/name): sha(H/'scripts'/name)
        for name in ['audit_full.py', 'check_complete.py', 'serialize_final.py', 'continue_after_replay.py']}
state = dict(status='WAITING_FOR_EXISTING_FULL_REPLAY', pid=os.getpid(),
             started_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
             source_files_sha256=pins, stages=[])

def save():
    tmp = receipt.with_suffix('.pending')
    tmp.write_text(json.dumps(state, indent=2)+'\n', encoding='utf-8')
    os.replace(tmp, receipt)

save()
try:
    while True:
        guard = read(H/'data/serialization-1793742438473223500.json')
        progress = read(P/'data/full-replay-progress.json')
        if guard['status'] == 'RESUMED':
            assert guard.get('transfer_exit_code') == 0, guard.get('exception', guard.get('transfer_exit_code'))
            assert guard['resume_return_code'] == 0
            assert progress['status'] == 'PASS_COMPLETE_FULL_REPLAY_MODULES'
            assert len(progress['checked_modules']) == 342 and progress['active'] is None
            break
        assert guard['status'] in ['RUNNING_FULL_REPLAY_ALONE', 'COORDINATOR_HELD']
        time.sleep(2)
    for name, label in [('audit_full.py', 'AUDITING_COMPLETE_REPLAY'), ('serialize_final.py', 'CHECKING_FINAL_CONSEQUENCE')]:
        for p, d in pins.items():
            assert sha(Path(p)) == d, p
        state['status'] = label
        save()
        log = H/'logs'/('continuation-'+name+'.log')
        log.parent.mkdir(exist_ok=True)
        assert not log.exists()
        with log.open('w', encoding='utf-8') as out:
            child = subprocess.Popen([sys.executable, '-B', '-X', 'utf8', str(H/'scripts'/name)], cwd=R,
                                     stdout=out, stderr=subprocess.STDOUT)
            state['active_pid'] = child.pid
            save()
            code = child.wait()
        state['stages'].append(dict(script=name, exit_code=code, log=str(log), log_sha256=sha(log)))
        state['active_pid'] = None
        save()
        assert code == 0, (name, code)
    final = read(H/'data/ShareComplete152-audit.json')
    assert final['status'] == 'PASS' and final['exit_code'] == 0 and final['stop_reason'] is None
    state.update(status='PASS_FINAL_ACTUAL_SNAKE_COMPOSITION',
                 final_receipt_sha256=sha(H/'data/ShareComplete152-audit.json'))
except BaseException as e:
    state.update(status='FAILED_REQUIRES_INSPECTION', exception=repr(e))
    raise
finally:
    state['finished_at'] = datetime.datetime.now(datetime.timezone.utc).isoformat()
    save()
    print(json.dumps({k:v for k,v in state.items() if k != 'source_files_sha256'}), flush=True)
