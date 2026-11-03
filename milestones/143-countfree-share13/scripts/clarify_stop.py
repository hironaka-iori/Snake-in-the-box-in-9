"""Clarify the launcher race without changing any original stop record or proof receipt."""
from pathlib import Path
import datetime,hashlib,json,subprocess
H=Path(__file__).resolve().parents[1];R=H.parents[1]
state=json.loads((H/'audit/replay-after-intentional-stop.json').read_text())
assert len(state['checked_modules'])==23 and state['active']['module']=='Share143.Shard19'
cmd="$p=@(Get-CimInstance Win32_Process | Where-Object {($_.Name -eq 'lean.exe' -or $_.Name -eq 'python.exe' -or $_.Name -eq 'lake.exe') -and $_.CommandLine -like '*143-countfree-share13*' -and ($_.CommandLine -like '*run_replay.py*' -or $_.Name -eq 'lean.exe' -or $_.Name -eq 'lake.exe')} | Select-Object ProcessId,Name,CommandLine);ConvertTo-Json -InputObject $p -Depth 3 -Compress"
live=json.loads(subprocess.check_output(['powershell','-NoProfile','-Command',cmd],text=True));assert live==[]
files=[H/'scripts/finish_documents.py',H/'MATHEMATICAL_NOTE.md',R/'handoff/NEXT_AGENT_PROMPT.md']
for p in files:
 s=p.read_text(encoding='utf-8')
 s=s.replace('termination between modules after the stronger obstruction superseded13.','termination after 23 completed modules, when the stronger obstruction superseded13.')
 s=s.replace('intentionally terminated between modules after the','intentionally terminated after 23 completed modules, following the')
 p.write_text(s,encoding='utf-8')
j=dict(status='CONFIRMED_NO_LIVE_SHARE143_REPLAY',recorded_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),checked_modules=23,last_saved_active=state['active'],live_replay_processes=live,explanation='The initial stop observation was between modules. Before the saved stop snapshots, the driver launched Share143.Shard19; its launcher was terminated with the driver. The next module has no successful receipt and is not counted. Original observations and termination output remain unchanged.',snapshots_sha256={n:hashlib.sha256((H/n).read_bytes()).hexdigest() for n in ['data/intentional-stop.json','audit/replay-after-intentional-stop.json']})
(H/'data/stop-observation-review.json').write_text(json.dumps(j,indent=2)+'\n',encoding='utf-8');print(j['status'])
