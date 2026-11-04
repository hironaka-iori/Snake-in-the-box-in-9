"""Recover accepted proof work after a verified reboot, without repeating it.

The old hold/continuation records remain historical evidence. No process is
resumed by PID, and no synthetic RESUMED receipt is produced.
"""
from pathlib import Path
import datetime, hashlib, json, os, subprocess, sys, time

H = Path(__file__).resolve().parents[1]
R = H.parents[1]
P = R/'milestones/151-countfree-replay-pilot'
read = lambda p: json.loads(p.read_text(encoding='utf-8-sig'))
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
target = H/'data/reboot-recovery-v2-progress.json'
assert not target.exists()
pause = read(R/'work/user-pause-153.json')
cmd = '''$o=Get-CimInstance Win32_OperatingSystem; @{boot_ms=([DateTimeOffset]$o.LastBootUpTime).ToUnixTimeMilliseconds(); processes=@(Get-CimInstance Win32_Process | Where-Object {$_.Name -eq 'python.exe' -or $_.Name -eq 'lean.exe'} | Select-Object ProcessId,ParentProcessId,Name,CreationDate,CommandLine)} | ConvertTo-Json -Depth 4 -Compress'''
snapshot = json.loads(subprocess.check_output(['powershell','-NoProfile','-Command',cmd],text=True))
pause_ms = int(datetime.datetime.fromisoformat(pause['recorded_at']).timestamp()*1000)
assert snapshot['boot_ms'] > pause_ms, 'A reboot after the recorded pause is required'
old_pids = {x['ProcessId'] for x in pause['suspended']} | {pause['already_held147_pid']}
assert not old_pids.intersection(x['ProcessId'] for x in snapshot['processes'])
assert not any(x['Name']=='lean.exe' for x in snapshot['processes'])
for row in snapshot['processes']:
    if row['ProcessId']==os.getpid(): continue
    command=(row['CommandLine'] or '').replace('\\','/')
    assert not ('Snake-in-a-box' in command and any(x in command for x in
        ['run_full_replay.py','check_full_replay.py','serialize_complete.py','continue_after_replay.py','check_complete.py'])), command
progress = read(P/'data/full-replay-progress.json')
assert progress['status']=='RUNNING' and len(progress['checked_modules'])==301
assert progress['pid'] in old_pids
lock=P/'data/full-replay-batch.lock'
assert not lock.exists()
assert read(H/'audit/reboot-recovery/full-replay-batch.lock')['pid']==progress['pid']
archive=H/'audit/reboot-recovery-v2'
archive.mkdir(parents=True,exist_ok=False)
historical = [R/'work/user-pause-153.json', P/'data/full-replay-progress.json', H/'audit/reboot-recovery/full-replay-batch.lock',
    H/'data/final-continuation-progress.json', H/'data/serialization-1793742438473223500.json']
saved=[]
for source in historical:
    destination=archive/source.name
    destination.write_bytes(source.read_bytes())
    assert sha(destination)==sha(source)
    saved.append(dict(source=str(source),archive=str(destination),sha256=sha(source)))
state=dict(status='RECOVERING_AFTER_VERIFIED_REBOOT',pid=os.getpid(),
    started_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
    boot_observation=snapshot,previous_accepted_modules=301,previous_processes_confirmed_absent=True,
    prior_attempt='Failed before dispatch because the logs directory was absent; exact source and failure record preserved.',
    historical_records=saved,stages=[],pins={str(p):sha(p) for p in [
        Path(__file__),P/'scripts/run_full_replay.py',P/'scripts/check_full_replay.py',
        H/'scripts/audit_full.py',H/'scripts/check_complete.py']},
    policy='Original driver revalidates and reuses every accepted receipt. The 147 job is absent after reboot; no hold or resume is needed.')
def save():
    temporary=target.with_suffix('.pending')
    temporary.write_text(json.dumps(state,indent=2)+'\n',encoding='utf-8')
    os.replace(temporary,target)
save()
# This is a stale lock owned by a process proved absent after the reboot.
assert not lock.exists()
(H/'logs').mkdir(exist_ok=True)
try:
    for script,arguments,label in [
        (P/'scripts/run_full_replay.py',[],'CHECKING_REMAINING_REPLAY'),
        (H/'scripts/audit_full.py',[],'AUDITING_COMPLETE_REPLAY'),
        (H/'scripts/check_complete.py',['ShareComplete152'],'CHECKING_ACTUAL_SNAKE_CONSEQUENCE')]:
        for path,digest in state['pins'].items(): assert sha(path)==digest,path
        state['status']=label
        log=H/'logs'/('reboot-recovery-'+script.name+'.log')
        assert not log.exists()
        with log.open('w',encoding='utf-8') as output:
            child=subprocess.Popen([sys.executable,'-B','-X','utf8',str(script),*arguments],
                cwd=R,stdout=output,stderr=subprocess.STDOUT)
            state['active_pid']=child.pid
            save()
            code=child.wait()
        state['stages'].append(dict(script=str(script),arguments=arguments,exit_code=code,
            log=str(log),log_sha256=sha(log)))
        state['active_pid']=None
        save()
        assert code==0,(script,code)
    final=read(H/'data/ShareComplete152-audit.json')
    assert final['status']=='PASS' and final['exit_code']==0 and final['stop_reason'] is None
    state.update(status='PASS_RECOVERED_ACTUAL_SNAKE_COMPOSITION',
        final_receipt_sha256=sha(H/'data/ShareComplete152-audit.json'))
except BaseException as error:
    state.update(status='FAILED_REQUIRES_INSPECTION',exception=repr(error))
    raise
finally:
    state['finished_at']=datetime.datetime.now(datetime.timezone.utc).isoformat()
    save()
    print(json.dumps({k:state[k] for k in ['status','previous_accepted_modules','stages']}),flush=True)
