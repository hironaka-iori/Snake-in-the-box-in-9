"""Save an exact accepted prefix while the existing full replay continues."""
from pathlib import Path
import datetime, hashlib, json, re, subprocess
H=Path(__file__).resolve().parents[1]; R=H.parents[1]
P=R/'milestones/151-countfree-replay-pilot'; Q=R/'milestones/147-countfree-clause-semantics'
read=lambda p:json.loads(Path(p).read_text(encoding='utf-8-sig'))
cache={}
def sha(p):
    p=Path(p); key=(str(p.resolve()),p.stat().st_size,p.stat().st_mtime_ns)
    if key not in cache:
        d=hashlib.sha256()
        with p.open('rb') as f:
            for b in iter(lambda:f.read(1048576),b''):d.update(b)
        cache[key]=d.hexdigest()
    return cache[key]
def write(p,data):
    assert not p.exists(),p
    p.write_text(json.dumps(data,indent=2)+'\n',encoding='utf-8')

progress_bytes=(P/'data/full-replay-progress.json').read_bytes()
progress=json.loads(progress_bytes)
assert progress['status']=='RUNNING' and 49<len(progress['checked_modules'])<342
guard_path=H/'data/serialization-1793742438473223500.json'
guard=read(guard_path); assert guard['status']=='RUNNING_FULL_REPLAY_ALONE'
continuation=read(H/'data/final-continuation-progress.json')
assert continuation['status']=='WAITING_FOR_EXISTING_FULL_REPLAY'
plan=read(P/'data/full-execution-plan.json')
assert sha(P/'data/full-execution-plan.json')==progress['plan_sha256']
assert sha(P/'scripts/check_full_replay.py')==progress['checker_sha256']
assert sha(P/'scripts/run_full_replay.py')==progress['driver_sha256']
assert [x['module'] for x in progress['checked_modules']]==plan['module_order'][:len(progress['checked_modules'])]
artifacts={a['module']:a for a in plan['artifacts']}; reports=0; files=set()
published={x['path']:x for x in read(P/'data/file-manifest.json')['files']}
for row in progress['checked_modules']:
    name=row['module']; rp=P/'data'/(name+'-audit.json'); q=read(rp)
    assert sha(rp)==row['receipt_sha256']
    assert q['status']=='PASS' and q['exit_code']==0 and q['stop_reason'] is None
    assert sha(q['source'])==q['source_sha256']==artifacts[name]['sha256']
    assert sha(q['object'])==q['olean_sha256'] and sha(q['log'])==q['log_sha256']
    log=Path(q['log']).parent
    assert sha(log/'source.lean.txt')==q['source_sha256']
    assert sha(log/'checker.py.txt')==q['checker_sha256']
    assert sha(log/'record.json')==sha(rp)
    for p,d in q['dependencies'].items():assert sha(p)==d,p
    text=Path(q['source']).read_text(encoding='utf-8')
    assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b',text)
    assert len(q['axioms'])==text.count('#print axioms')
    assert all(set(a['axioms'])<={'propext','Classical.choice','Quot.sound'} for a in q['axioms'])
    reports+=len(q['axioms'])
    for p in [rp,*log.iterdir()]:
        rel=p.relative_to(R).as_posix()
        if rel in published:assert sha(p)==published[rel]['sha256']
        else:files.add(p)
for p,d in read(H/'audit/completion-source-review.json')['pins'].items():assert sha(R/p)==d,p
assert sha(H/'audit/completion-source-review.json')=='2f5b106b50a811dab02c0df9f72f3c4b4b5c7cd7ac798f3df21155fd174f0c65'
assert sha(H/'scripts/serialize_complete.py')==sha(H/'audit/active-controller.exact.py')
assert read(H/'data/pending-guard-tests.json')['status']=='PASS_INCOMPLETE_REPLAY_REJECTED'
for p,d in continuation['source_files_sha256'].items():assert sha(p)==d,p
processes=json.loads(subprocess.check_output(['powershell','-NoProfile','-Command',
    '@(Get-CimInstance Win32_Process | Where-Object { $_.Name -eq "python.exe" -or $_.Name -eq "lean.exe" } | Select-Object ProcessId,ParentProcessId,Name,CommandLine,CreationDate) | ConvertTo-Json -Compress'],text=True))
by_pid={x['ProcessId']:x for x in processes}
for pid in [guard['controller_pid'],guard['watchdog_pid'],guard['transfer_driver_pid'],guard['replay_pid'],continuation['pid']]:assert pid in by_pid,pid
assert by_pid[guard['replay_pid']]['CreationDate']==guard['replay_process']['CreationDate']
assert by_pid[guard['transfer_driver_pid']]['ParentProcessId']==guard['controller_pid']
protected=read(P/'data/checkpoint.json')['protected_unrelated_files_sha256']
for p,d in protected.items():assert sha(R/p)==d,p
paper=R/'paper/snake9_research.tex'; editor=Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex')
assert paper.read_bytes()==editor.read_bytes()
assert sha(paper)=='4d4c7a43d188d05bef483f30e4c55892cceb45b1978f2a6e4d188927eb262bcd'
snapshot=H/'data/replay-prefix-snapshot.json'; assert not snapshot.exists();snapshot.write_bytes(progress_bytes)
write(H/'data/serialization-observation.json',guard)
write(H/'data/continuation-observation.json',continuation)
write(H/'data/process-observation.json',processes)
write(H/'data/accepted-prefix-files.json',dict(status='PASS_NEW_ACCEPTED_REPLAY_PREFIX_FILES',files=[
    dict(path=p.relative_to(R).as_posix(),bytes=p.stat().st_size,sha256=sha(p)) for p in sorted(files)]))
record=dict(status='PASS_ACCEPTED_PREFIX_FULL_REPLAY_RUNNING',goal_status='ACTIVE',
    recorded_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
    base_commit='8d0b401abe15380a77082dae01bba8f4564e26ad',
    accepted151_modules=len(progress['checked_modules']),total151_modules=342,accepted_axiom_reports=reports,
    replay_complete=False,actual_snake_share16_complete=False,new_global_upper_bound=False,
    current_interval=[191,235],interval_scope='Maintained contributor theorem; independent complete rebuild remains pending.',
    conditional234_other_premises_unchanged=True,
    active151_session=67715,active151_controller_pid=guard['controller_pid'],active151_driver_pid=guard['transfer_driver_pid'],
    held147_session=67526,held147_pid=guard['replay_pid'],held147_is_active_compiler=False,
    queued_final_session=80927,queued_final_pid=continuation['pid'],
    final_work='Already queued: complete replay audit, then short guarded actual-snake composition. Do not launch another continuation.',
    next_after_final='Run scripts/audit_actual.py after final composition succeeds; then the guarded paper update, source checks and built-in compilation. Publish complete evidence in a separate exact completion manifest without changing this running checkpoint.',
    failed_stronger_query='Cap16 / target17 TIMEOUT; unresolved. Partial output retained in verified archive.',
    immutable_snapshot_sha256=sha(snapshot),paper_sha256=sha(paper),paper_changed=False,pdf_rebuilt=False,
    live_files_excluded=True,full_paper_revision_last=146,full_paper_revision_next=156,
    protected_unrelated_files_sha256=protected,
    preparation_issue='The pending-guard checks passed. Their subsequent controller-copy step initially failed because audit/ was absent; the directory and exact snapshot were then created. No Lean check failed.')
write(H/'data/checkpoint.json',record)
print(json.dumps({k:v for k,v in record.items() if k!='protected_unrelated_files_sha256'}))
