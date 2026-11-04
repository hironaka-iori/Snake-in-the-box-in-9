"""Audit every saved module of the full shared share17 contradiction."""
from pathlib import Path
import argparse, hashlib, json, re, subprocess, sys

H=Path(__file__).resolve().parents[1];R=H.parents[1]
P=R/'milestones/153-pair-conditioned-share17/replay'
read=lambda p:json.loads(Path(p).read_text(encoding='utf-8-sig'))
cache={}
def sha(path):
    path=Path(path);key=(str(path.resolve()),path.stat().st_size,path.stat().st_mtime_ns)
    if key not in cache:
        digest=hashlib.sha256()
        with path.open('rb') as stream:
            for block in iter(lambda:stream.read(1048576),b''):digest.update(block)
        cache[key]=digest.hexdigest()
    return cache[key]

ap=argparse.ArgumentParser();ap.add_argument('--verify-only',action='store_true');args=ap.parse_args()
progress_path=H/'data/full-replay-progress.json'
if not progress_path.exists():
    print(json.dumps(dict(status='WAITING_FOR_FULL_REPLAY')));raise SystemExit(2)
progress=read(progress_path)
if progress['status']!='PASS_COMPLETE_FULL_REPLAY_MODULES' or progress['active'] is not None:
    print(json.dumps(dict(status='WAITING_FOR_COMPLETE_FULL_REPLAY',progress_status=progress['status'],checked=len(progress['checked_modules']))))
    raise SystemExit(2)
assert not (H/'data/full-replay-batch.lock').exists()
planpath=H/'data/full-source-plan.json';plan=read(planpath)
preppath=H/'data/full-execution-preparation.json';prep=read(preppath)
assert prep['status']=='PREPARED_FULL_SHARED_CORE_REPLAY_UNCHECKED'
assert len(plan['module_order'])==len(progress['checked_modules'])==137
assert [row['module'] for row in progress['checked_modules']]==plan['module_order']
assert sha(planpath)==progress['plan_sha256']==prep['full_plan_sha256']
assert sha(H/'scripts/run_full_replay.py')==progress['driver_sha256']
assert sha(H/'scripts/check_full_replay.py')==progress['checker_sha256']
for name,digest in prep['execution_scripts_sha256'].items():assert sha(H/name)==digest,name
for field in ['input_pins','original_source_pins']:
    for path,digest in prep[field].items():assert sha(R/path)==digest,path
subprocess.run([sys.executable,'-B','-X','utf8',str(H/'scripts/finish_pilot_v2.py'),'--verify-only'],cwd=R,check=True)
pilot=read(H/'data/pilot-completion-v2.json')
assert pilot['status']=='PASS_14BIT_INITIAL_TREE_AND_CHECKPOINT_PILOT' and pilot['checked_modules']==34
artifacts={row['module']:row for row in plan['artifacts']}
progress_rows={row['module']:row for row in progress['checked_modules']}
rows=[];reports=0;peak=0
for module in plan['module_order']:
    path=H/'data'/(module+'-audit.json');receipt=read(path)
    assert sha(path)==progress_rows[module]['receipt_sha256']
    assert receipt['status']=='PASS' and receipt['exit_code']==0 and receipt['stop_reason'] is None,module
    source=H/artifacts[module]['path']
    assert Path(receipt['source']).resolve()==source.resolve()
    assert sha(source)==receipt['source_sha256']==artifacts[module]['sha256']
    assert Path(receipt['object']).resolve()==(H/'build'/(module.replace('.','/')+'.olean')).resolve()
    assert sha(receipt['object'])==receipt['olean_sha256']
    assert sha(receipt['log'])==receipt['log_sha256']
    folder=Path(receipt['log']).parent
    assert sha(folder/'source.lean.txt')==receipt['source_sha256']
    assert sha(folder/'checker.py.txt')==receipt['checker_sha256']
    if module in prep['reused_pilot_receipts']:
        previous=prep['reused_pilot_receipts'][module]
        assert sha(path)==previous['receipt_sha256'] and receipt['checker_sha256']==previous['checker_sha256']
    else:
        assert receipt['checker_sha256']==progress['checker_sha256']
    for dependency,digest in receipt['dependencies'].items():assert sha(dependency)==digest,dependency
    text=source.read_text(encoding='utf-8')
    assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b',text)
    assert len(receipt['axioms'])==text.count('#print axioms')
    assert all(set(row['axioms'])<={'propext','Classical.choice','Quot.sound'} for row in receipt['axioms'])
    reports+=len(receipt['axioms'])
    for sample in receipt['resource_samples']:
        for process in sample['owned_lean_processes']:peak=max(peak,int(process['PrivatePageCount']))
    rows.append(dict(module=module,receipt=path.relative_to(H).as_posix(),sha256=sha(path),
        checker_sha256=receipt['checker_sha256'],axioms=receipt['axioms'],
        compiler_wall_seconds=receipt['compiler_wall_seconds'],seconds=receipt['seconds']))
assert reports==407
assert len(prep['reused_pilot_receipts'])==34
assert plan['module_order'][-1]=='ReplayUnsat153'
finalpath=H/'data/ReplayUnsat153-audit.json';final=read(finalpath)
assert len(final['axioms'])==1 and final['axioms'][0]['theorem']=='Snake9.ReplayFull153.unsat'
finaltext=Path(final['source']).read_text(encoding='utf-8')
assert 'theorem unsat : Snake9.LocalWindow.Unsat Snake9.LocalWindow.ShareWindow153.cnf := by' in finaltext
nativepath=P/'data/packed-replay.json';native=read(nativepath)
assert native['status']=='PASS_COMPLETE_RENAMED_AND_PACKED_RUP_REPLAY' and native['final_empty']
assert (native['deductions'],native['hints'],native['final_original_clause_id'],native['final_tree_key'])==(30305,1754767,190427,4398)
assert len(native['segments'])==290
assert native['segments'][0]['first_step']==0 and native['segments'][-1]['after_step']==30305
assert all(a['after_step']==b['first_step'] for a,b in zip(native['segments'],native['segments'][1:]))
assert sum(row['hints'] for row in native['segments'])==1754767
for row in native['artifacts']+native['checkpoints']:assert sha(P/row['path'])==row['sha256'],row['path']
sizing=read(P/'data/sizing.json')
assert (sizing['core_clauses'],sizing['tree_height'],sizing['segment_count'])==(11869,14,290)
sharedpath=R/'milestones/154-share17-broader-semantics/data/LocalWindowCnf.ShareWindow153-audit.json'
shared=read(sharedpath)
assert shared['status']=='PASS' and shared['exit_code']==0 and shared['stop_reason'] is None
assert shared['source_sha256']==prep['shared_cnf_source_sha256']==sha(shared['source'])
assert sha(shared['object'])==shared['olean_sha256'] and sha(shared['log'])==shared['log_sha256']
for dependency,digest in shared['dependencies'].items():assert sha(dependency)==digest,dependency
record=dict(status='PASS_COMPLETE_SHARED_SHARE17_CORE_CONTRADICTION',checked_modules=137,
    reused_pilot_modules=34,new_modules=103,axiom_reports=407,
    initial_core_clauses=11869,tree_height=14,segments=290,deductions=30305,references=1754767,
    final_original_clause_id=190427,final_tree_key=4398,
    final_theorem='Snake9.ReplayFull153.unsat',final_CNF='Snake9.LocalWindow.ShareWindow153.cnf',
    complete_shared_core_contradiction=True,actual_snake_share17_complete=False,new_global_upper_bound=False,
    maximum_sampled_private_bytes=peak,compiler_wall_seconds=sum(row['compiler_wall_seconds'] for row in rows),
    receipts=rows,source_files_sha256={path.relative_to(R).as_posix():sha(path) for path in
        [Path(__file__),planpath,preppath,progress_path,nativepath,P/'data/sizing.json',sharedpath,finalpath,H/'data/pilot-completion-v2.json']},
    scope='The complete contradiction of the exact shared compact CNF is accepted. Composition with the separately checked broader actual-snake implication is still required. This audit supplies no new global snake bound.')
target=H/'data/full-replay-completion.json'
if args.verify_only:
    assert target.exists() and read(target)==record
else:
    assert not target.exists();target.write_bytes((json.dumps(record,indent=2)+'\n').encode('utf-8'))
print(json.dumps({k:v for k,v in record.items() if k not in ['receipts','source_files_sha256']}))
