"""Accept the complete saved153 initial-tree/prefix pilot; never invoke Lean."""
from pathlib import Path
import argparse, hashlib, json, re

H=Path(__file__).resolve().parents[1]
R=H.parents[1]
P=R/'milestones/153-pair-conditioned-share17/replay'
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

ap=argparse.ArgumentParser();ap.add_argument('--verify-only',action='store_true');args=ap.parse_args()
progress_path=H/'data/replay-progress-v2.json'
if not progress_path.exists():
    print(json.dumps(dict(status='WAITING_FOR_PILOT_CHECKS')))
    raise SystemExit(2)
plan=read(H/'data/pilot-source-plan.json');progress=read(progress_path)
if progress['status']!='PASS_COMPLETE_REPLAY_PILOT' or progress['active'] is not None:
    print(json.dumps(dict(status='WAITING_FOR_COMPLETE_PILOT',progress_status=progress['status'],checked=len(progress['checked_modules']))))
    raise SystemExit(2)
assert not (H/'data/replay-batch-v2.lock').exists()
prep=read(H/'data/preparation-v2.json')
assert prep['status']=='PREPARED_NATIVE_RESOURCE_PILOT_EXECUTION_UNCHECKED'
assert sha(H/'data/pilot-source-plan.json')==progress['plan_sha256']==prep['pilot_plan_sha256']
assert sha(H/'scripts/run_replay_v2.py')==progress['driver_sha256']
assert sha(H/'scripts/check_replay_v2.py')==progress['checker_sha256']
for name,digest in prep['execution_scripts_sha256'].items():assert sha(H/name)==digest,name
for path,digest in prep['original_source_pins'].items():assert sha(R/path)==digest,path
for path,digest in prep['input_pins'].items():assert sha(R/path)==digest,path
assert len(plan['module_order'])==len(progress['checked_modules'])==34
assert [row['module'] for row in progress['checked_modules']]==plan['module_order']
artifacts={row['module']:row for row in plan['artifacts']}
progress_rows={row['module']:row for row in progress['checked_modules']}
rows=[];peak=0
for module in plan['module_order']:
    path=H/'data'/(module+'-audit.json');receipt=read(path)
    assert sha(path)==progress_rows[module]['receipt_sha256']
    assert receipt['status']=='PASS' and receipt['exit_code']==0 and receipt['stop_reason'] is None,module
    source=H/artifacts[module]['path']
    assert Path(receipt['source']).resolve()==source.resolve()
    assert sha(source)==receipt['source_sha256']==artifacts[module]['sha256']
    assert Path(receipt['object']).resolve()==(H/'build'/(module.replace('.','/')+'.olean')).resolve()
    assert sha(receipt['object'])==receipt['olean_sha256'] and sha(receipt['log'])==receipt['log_sha256']
    folder=Path(receipt['log']).parent
    assert sha(folder/'source.lean.txt')==receipt['source_sha256']
    assert sha(folder/'checker.py.txt')==receipt['checker_sha256']==progress['checker_sha256']
    for dependency,digest in receipt['dependencies'].items():assert sha(dependency)==digest,dependency
    text=source.read_text(encoding='utf-8')
    assert len(receipt['axioms'])==text.count('#print axioms')
    assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b',text)
    assert all(set(row['axioms'])<={'propext','Classical.choice','Quot.sound'} for row in receipt['axioms'])
    for sample in receipt['resource_samples']:
        for process in sample['owned_lean_processes']:peak=max(peak,int(process['PrivatePageCount']))
    rows.append(dict(module=module,receipt=path.relative_to(H).as_posix(),sha256=sha(path),
        axioms=receipt['axioms'],compiler_wall_seconds=receipt['compiler_wall_seconds'],seconds=receipt['seconds']))
for path,digest in plan['copied_source_pins'].items():assert sha(R/path)==digest,path
native_path=P/'data/packed-replay.json';native=read(native_path)
assert native['status']=='PASS_COMPLETE_RENAMED_AND_PACKED_RUP_REPLAY'
assert (native['deductions'],native['hints'],native['final_original_clause_id'],native['final_tree_key'])==(30305,1754767,190427,4398)
assert native['final_empty']
for row in native['artifacts']+native['checkpoints']:assert sha(P/row['path'])==row['sha256'],row['path']
assert native['segments'][0]['after_step']==2095 and native['segments'][0]['hints']==6002
assert plan['initial_subtrees']==93
final=read(H/'data/ReplayPilotConsequence153-audit.json')
assert len(final['axioms'])==1 and final['axioms'][0]['theorem']=='Snake9.ReplayPilot153.prefix_true'
shared_path=R/'milestones/154-share17-broader-semantics/data/LocalWindowCnf.ShareWindow153-audit.json'
shared=read(shared_path)
assert shared['status']=='PASS' and shared['exit_code']==0 and shared['stop_reason'] is None
assert shared['source_sha256']==prep['shared_cnf_source_sha256']==sha(shared['source'])
assert sha(shared['object'])==shared['olean_sha256'] and sha(shared['log'])==shared['log_sha256']
for path,digest in shared['dependencies'].items():assert sha(path)==digest,path
record=dict(status='PASS_14BIT_INITIAL_TREE_AND_CHECKPOINT_PILOT',checked_modules=34,
    axiom_reports=sum(len(row['axioms']) for row in rows),initial_core_clauses=11869,initial_subtrees=93,
    deductions_checked=2095,references_checked=6002,full_checkpoint_checked=True,
    maximum_sampled_private_bytes=peak,compiler_wall_seconds=sum(row['compiler_wall_seconds'] for row in rows),
    complete_numerical_replay_deductions=30305,complete_numerical_replay_references=1754767,
    full_Lean_replay_complete=False,actual_snake_share17_complete=False,new_global_upper_bound=False,
    receipts=rows,source_files_sha256={path.relative_to(R).as_posix():sha(path) for path in
        [Path(__file__),H/'data/pilot-source-plan.json',progress_path,native_path,H/'data/preparation-v2.json',shared_path]},
    scope='The exact shared core implies truth of the materialized initial tree and complete checkpoint after2095 deductions. The complete contradiction and actual-snake consequence remain separate obligations. No historical suspended-process claim is required or made.')
target=H/'data/pilot-completion-v2.json'
if args.verify_only:
    assert target.exists() and read(target)==record
else:
    assert not target.exists()
    target.write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:v for k,v in record.items() if k not in ['receipts','source_files_sha256']}))
