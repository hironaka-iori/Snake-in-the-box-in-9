"""Stop only the live143 replay after a stronger graph obstruction supersedes floor13."""
from pathlib import Path
import datetime,hashlib,json,subprocess
H=Path(__file__).resolve().parents[1]
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
p=H/'data/replay-progress-base.json';lock=H/'data/replay-base.lock';state=read(p);pid=state['pid']
assert state['status']=='RUNNING' and read(lock)['pid']==pid
cmd=f"Get-CimInstance Win32_Process -Filter \"ProcessId={pid}\" | Select-Object ProcessId,Name,CommandLine | ConvertTo-Json -Compress"
proc=json.loads(subprocess.check_output(['powershell','-NoProfile','-Command',cmd],text=True))
assert proc['ProcessId']==pid and proc['Name']=='python.exe' and '143-countfree-share13/scripts/run_replay.py' in proc['CommandLine'].replace('\\','/')
(H/'audit/replay-before-intentional-stop.json').write_bytes(p.read_bytes())
result=subprocess.run(['taskkill','/PID',str(pid),'/T','/F'],capture_output=True,text=True,check=True)
dead=subprocess.check_output(['powershell','-NoProfile','-Command',cmd],text=True).strip();assert not dead
(H/'audit/replay-after-intentional-stop.json').write_bytes(p.read_bytes())
lock.rename(H/'audit/replay-stopped.lock.txt')
j=dict(status='INTENTIONALLY_STOPPED_SUPERSEDED_SHARE13_TARGET',recorded_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),driver=proc,termination_stdout=result.stdout,termination_stderr=result.stderr,exit_code=result.returncode,checked_modules=len(read(p)['checked_modules']),total_modules=state['total_modules'],active_module_at_observation=state.get('active'),snapshots={n:sha(H/n) for n in ['audit/replay-before-intentional-stop.json','audit/replay-after-intentional-stop.json','audit/replay-stopped.lock.txt']},reason='A zero-event cycle and a five-edge subwalk rule out any share floor at most14 for the current comparison, even with an optimal potential and any nonnegative uniform credit. Preserve the cap12 native certificate and every successful Lean receipt. No actual share13 theorem has completed.',goal_status='ACTIVE',other_batches_touched=False)
(H/'data/intentional-stop.json').write_text(json.dumps(j,indent=2)+'\n',encoding='utf-8');print(json.dumps(j))
