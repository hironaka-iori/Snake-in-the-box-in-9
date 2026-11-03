"""Audit the exact conditional actual-snake transfer and its reuse boundary."""
from pathlib import Path
import hashlib,json,re,subprocess,datetime,zipfile
H=Path(__file__).resolve().parents[1];R=H.parents[1];Q=R/'milestones/147-countfree-clause-semantics'
read=lambda p:json.loads(Path(p).read_text(encoding='utf-8-sig'))
cache={}
def sha(p):
    p=Path(p);key=(str(p.resolve()),p.stat().st_size,p.stat().st_mtime_ns)
    if key not in cache:
        d=hashlib.sha256()
        with p.open('rb') as f:
            for b in iter(lambda:f.read(1048576),b''):d.update(b)
        cache[key]=d.hexdigest()
    return cache[key]
planpath=H/'data/transfer-plan-v4.json';plan=read(planpath);progress=read(H/'data/transfer-v4-progress.json')
assert progress['status']=='PASS_COMPLETE_CONDITIONAL_TRANSFER_CHAIN' and progress['active'] is None
assert len(progress['checked_modules'])==len(plan['module_order'])==16
assert not (H/'data/transfer-v4-batch.lock').exists()
artifacts={x['module']:x for x in plan['artifacts']};rows=[];peak=0
known_comment="/- A snake's length is its number of edges. No optimality axiom is declared. -/"
for item in progress['checked_modules']:
    m=item['module'];p=H/'data'/(m+'-audit.json');j=read(p)
    assert sha(p)==item['receipt_sha256'] and j['status']=='PASS' and j['exit_code']==0 and j['stop_reason'] is None
    assert sha(j['source'])==j['source_sha256']==artifacts[m]['sha256']
    assert sha(j['object'])==j['olean_sha256'] and sha(j['log'])==j['log_sha256']
    folder=Path(j['log']).parent
    assert sha(folder/'source.lean.txt')==j['source_sha256'] and sha(folder/'checker.py.txt')==j['checker_sha256']
    for p,d in j['dependencies'].items():assert sha(p)==d,p
    text=Path(j['source']).read_text(encoding='utf-8')
    assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b',text.replace(known_comment,''))
    assert len(j['axioms'])==text.count('#print axioms')
    assert all(set(a['axioms'])<={'propext','Classical.choice','Quot.sound'} for a in j['axioms'])
    for sample in j['resource_samples']:
        for proc in sample['owned_lean_processes']:peak=max(peak,int(proc['PrivatePageCount']))
    rows.append(dict(module=m,receipt=(H/'data'/(m+'-audit.json')).relative_to(H).as_posix(),
        sha256=sha(H/'data'/(m+'-audit.json')),axioms=j['axioms'],compiler_wall_seconds=j['compiler_wall_seconds']))
assert sum(len(x['axioms']) for x in rows)==27
reuse=read(H/'data/reused-data-object.json');assert reuse['status']=='PASS_PINNED_HISTORICAL_DATA_OBJECT_REUSE' and not reuse['fresh_compilation']
for p,d in reuse['source_files_sha256'].items():assert sha(p)==d,p
core=read(H/'data/core-source-review.json');direction=read(H/'data/direction-source-review.json')
assert sha(H/'lean-core/Snake9.lean')==core['core_sha256']
assert sha(H/'lean-core/DirectionWindowBridge.lean')==direction['extracted_sha256']
original=(H/'lean/Snake9.lean').read_bytes()
assert original.split(b'-- BEGIN WITNESS',1)[0]+b'end Snake9\n'==(H/'lean-core/Snake9.lean').read_bytes()
serial=[]
for p in sorted((H/'data').glob('serialization-*.json')):
    j=read(p);assert j['status']=='RESUMED' and j['resume_return_code']==0
    serial.append(dict(path=p.relative_to(H).as_posix(),sha256=sha(p),replay_pid=j['replay_pid'],transfer_exit_code=j['transfer_exit_code']))
assert len(serial)==4 and all(x['replay_pid']==15228 for x in serial)
assert serial[-1]['transfer_exit_code']==0
live=read(Q/'replay/data/full-replay-progress.json');assert live['status']=='RUNNING' and live['pid']==15228
cmd='Get-CimInstance Win32_Process -Filter "ProcessId=15228" | Select-Object ProcessId,CommandLine,CreationDate | ConvertTo-Json -Compress'
proc=json.loads(subprocess.check_output(['powershell','-NoProfile','-Command',cmd],text=True))
assert proc['ProcessId']==15228 and 'run_full_replay.py' in proc['CommandLine']
out=dict(status='PASS_CONDITIONAL_ACTUAL_SNAKE_SHARE16_TRANSFER',checked_modules=16,axiom_reports=27,
    freshly_checked_project_helpers=13,new_conditional_wrappers=2,reused_data_axiom_audits=1,
    inherited_data_object_reused=True,inherited_data_fresh_compilation=False,
    original_generic_definitions_preserved=True,selected_direction_proofs_preserved=True,
    coordinate_and_reversal_transfer_checked=True,extra_count_parity_or_endpoint_location_premises=False,
    remaining_mathematical_premise='Unsat of the exact012301 cap15 core, or its equivalent local RefutedShare premise.',
    theorem_scope='Every Snake m and fitting six-transition window whose forward or reversed canonical directions equal012301 has five-centre integer share sum at least16, conditional on the exact core refutation.',
    core_unsat_Lean_complete=False,unconditional_actual_snake_share16_complete=False,new_global_upper_bound=False,
    maximum_sampled_private_bytes=peak,compiler_seconds=sum(x['compiler_wall_seconds'] for x in rows),
    receipts=rows,serialization_records=serial,live_replay_process=proc,
    live_replay_modules_observed=len(live['checked_modules']),live_replay_total_modules=live['total_modules'],
    recorded_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
    evidence_sha256={p.relative_to(H).as_posix():sha(p) for p in [planpath,H/'data/transfer-v4-progress.json',H/'data/reused-data-object.json',H/'data/core-source-review.json',H/'data/direction-source-review.json',H/'audit/import-review.json']},
    trust_scope='Standard Lean and Mathlib libraries remain trusted with pinned entry artifacts. One historical automaton data object is reused with exact source/object/log/dependency hashes and fresh axiom reports. All other additional project helpers were compiled in148;147 model and semantic receipts remain pinned.')
dest=H/'data/transfer-completion.json';assert not dest.exists();dest.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8',newline='\n')
archive=H/'archives/inherited-data.zip';archive.parent.mkdir(exist_ok=True);assert not archive.exists()
members=[H/'lean/WindowAutomatonData.lean',Path(reuse['object']),H/'data/reused-data-object.json',Path(reuse['original_log'])]
record=[]
with zipfile.ZipFile(archive,'w',compression=zipfile.ZIP_DEFLATED,compresslevel=6) as z:
    for p in members:
        name=p.relative_to(R).as_posix();z.write(p,name);record.append(dict(path=name,bytes=p.stat().st_size,sha256=sha(p)))
with zipfile.ZipFile(archive) as z:
    for x in record:assert hashlib.sha256(z.read(x['path'])).hexdigest()==x['sha256']
ar=dict(status='PASS_BYTE_VERIFIED_INHERITED_DATA_ARCHIVE',path=archive.relative_to(R).as_posix(),sha256=sha(archive),members=record)
(H/'data/inherited-data-archive.json').write_text(json.dumps(ar,indent=2)+'\n',encoding='utf-8',newline='\n')
print(json.dumps({k:out[k] for k in ['status','checked_modules','axiom_reports','maximum_sampled_private_bytes','unconditional_actual_snake_share16_complete','live_replay_modules_observed']}))
