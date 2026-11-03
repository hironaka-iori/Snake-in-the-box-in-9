"""Prepare the short, separately guarded final composition run."""
from pathlib import Path
import hashlib, json

H = Path(__file__).resolve().parents[1]
read = lambda p: json.loads(p.read_text(encoding='utf-8-sig'))
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
source = H / 'scripts/serialize_complete.py'
s = source.read_text(encoding='utf-8')

def change(old, new):
    global s
    assert s.count(old) == 1, (old, s.count(old))
    s = s.replace(old, new)

change('"""Run the complete012032 replay alone and preserve the existing012301 job.\n\nThe watchdog waits for an orphaned owned replay driver, not merely for a\ngap between compilers, before resuming the held coordinator.\n"""',
       '"""Check the final actual-snake consequence after complete replay acceptance.\n\nPreserve the same012301 coordinator. The watchdog waits for the owned\nchecker, including its preflight, before resuming the held coordinator.\n"""')
change("'151-countfree-replay-pilot/scripts/run_full_replay.py'", "'152-countfree-share16-completion/scripts/check_complete.py'")
start = s.index("prep=read(H/'data/preparation.json')")
end = s.index("progress=read(Q/'replay/data/full-replay-progress.json')", start)
s = s[:start] + '''prep=read(H/'data/completion-preparation.json')
for path,d in prep['source_files_sha256'].items():
    assert hashlib.sha256(Path(path).read_bytes()).hexdigest()==d,path
complete=read(H/'data/replay-completion.json')
assert complete['status']=='PASS_COMPLETE_012032_CORE_CONTRADICTION'
assert complete['checked_modules']==342
original=read(H/'data/serialization-1793742438473223500.json')
assert original['status']=='RESUMED' and original['transfer_exit_code']==0
assert original['resume_return_code']==0
assert not (P/'data/full-replay-batch.lock').exists()
newprogress=read(P/'data/full-replay-progress.json')
assert newprogress['status']=='PASS_COMPLETE_FULL_REPLAY_MODULES'
assert newprogress['active'] is None and len(newprogress['checked_modules'])==342
assert not (H/'data/ShareComplete152-audit.json').exists()
''' + s[end:]
change("('serialization-'+str(time.time_ns())+'.json')", "('serialization-final-'+str(time.time_ns())+'.json')")
change("scope='Preserve same147 coordinator; run remaining151 full replay alone. A watchdog waits for an orphaned owned full driver before resuming147.'", "scope='Preserve same147 coordinator; check the final actual-snake theorem alone after complete replay audit. Watchdog waits for the owned checker before resuming147.'")
change("status='RUNNING_FULL_REPLAY_ALONE'", "status='RUNNING_FINAL_COMPOSITION_ALONE'")
change("'CURRENT147_CHECK_FINISHED; RUNNING_COMPLETE012032_REPLAY'", "'CURRENT147_CHECK_FINISHED; CHECKING_FINAL012032_SHARE16'")
change("str(P/'scripts/run_full_replay.py')", "str(H/'scripts/check_complete.py'),'ShareComplete152'")
change("while any(x['Name']=='lean.exe' for x in snapshot()):time.sleep(2)",
       "while any(x['Name']=='lean.exe' or (is_new_driver(x) and x['ParentProcessId']==os.getpid()) for x in snapshot()):time.sleep(2)")
target = H / 'scripts/serialize_final.py'
assert not target.exists()
compile(s, str(target), 'exec')
target.write_text(s, encoding='utf-8', newline='\n')
record = dict(status='PREPARED_FINAL_SERIALIZER_NOT_EXECUTED',
              source_files_sha256={str(p): sha(p) for p in [source, target, Path(__file__)]},
              requires_complete_replay_and_audit=True,
              requires_prior_coordinator_resumed=True)
(H/'data/final-runner-preparation.json').write_text(json.dumps(record, indent=2)+'\n', encoding='utf-8')
print(record['status'])
