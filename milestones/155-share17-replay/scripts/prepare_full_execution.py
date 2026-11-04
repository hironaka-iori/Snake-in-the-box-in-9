"""Prepare the full replay runner only after the accepted pilot and full export.

No compiler is invoked. --check-source-only validates generated Python in memory
and reports prerequisite presence without writing any generated file.
"""
from pathlib import Path
import argparse, ast, copy, hashlib, json, re, subprocess, sys

H=Path(__file__).resolve().parents[1];R=H.parents[1]
P=R/'milestones/153-pair-conditioned-share17/replay'
read=lambda p:json.loads(Path(p).read_text(encoding='utf-8-sig'))
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()

def once(text,old,new):
    assert text.count(old)==1,(old,text.count(old));return text.replace(old,new)

def texts():
    checker=(H/'scripts/check_replay_v2.py').read_text(encoding='utf-8')
    checker=checker.replace('data/pilot-source-plan.json','data/full-source-plan.json')
    checker=checker.replace('data/preparation-v2.json','data/full-execution-preparation.json')
    checker=checker.replace('PREPARED_NATIVE_RESOURCE_PILOT_EXECUTION_UNCHECKED','PREPARED_FULL_SHARED_CORE_REPLAY_UNCHECKED')
    checker=checker.replace("prep['pilot_plan_sha256']","prep['full_plan_sha256']")
    checker=checker.replace('scripts/check_replay_v2.py','scripts/check_full_replay.py')
    checker=once(checker,
        "assert sha(planpath)==prep['full_plan_sha256']",
        "assert sha(planpath)==prep['full_plan_sha256']\n"
        "assert a.module not in prep['pilot_module_order'], 'Reuse the accepted pilot receipt; never recompile it here'\n"
        "for p,d in prep['input_pins'].items():assert sha(R/p)==d,p")
    checker=once(checker,
        "for p,d in prep['original_source_pins'].items():deps[str(R/p)]=d",
        "for p,d in prep['original_source_pins'].items():deps[str(R/p)]=d\n"
        "for p,d in prep['input_pins'].items():deps[str(R/p)]=d")
    checker=once(checker,
        "    assert q['status']=='PASS' and q['exit_code']==0 and q['stop_reason'] is None",
        "    assert q['status']=='PASS' and q['exit_code']==0 and q['stop_reason'] is None\n"
        "    if name in prep['reused_pilot_receipts']:\n"
        "        previous=prep['reused_pilot_receipts'][name]\n"
        "        assert sha(rp)==previous['receipt_sha256'] and q['checker_sha256']==previous['checker_sha256']\n"
        "    elif name in expected:\n"
        "        assert q['checker_sha256']==sha(H/'scripts/check_full_replay.py')")
    checker=checker.replace('The34 pilot modules are freshly checked.',
        'The34 accepted pilot modules are reused with their original checker receipts; the remaining103 full-replay modules are checked separately.')
    assert "prep['pilot_plan_sha256']" not in checker
    assert 'Get-CimInstance' not in checker

    runner=(H/'scripts/run_replay_v2.py').read_text(encoding='utf-8')
    runner=runner.replace('data/pilot-source-plan.json','data/full-source-plan.json')
    runner=runner.replace('data/preparation-v2.json','data/full-execution-preparation.json')
    runner=runner.replace("prep['pilot_plan_sha256']","prep['full_plan_sha256']")
    runner=runner.replace('scripts/run_replay_v2.py','scripts/run_full_replay.py')
    runner=runner.replace('scripts/check_replay_v2.py','scripts/check_full_replay.py')
    runner=runner.replace('data/replay-batch-v2.lock','data/full-replay-batch.lock')
    runner=runner.replace('data/replay-progress-v2.json','data/full-replay-progress.json')
    runner=runner.replace("'replay-batch-v2-'","'full-replay-batch-'")
    runner=runner.replace("'replay-launch-v2-'","'full-replay-launch-'")
    runner=runner.replace('PASS_BOUNDED_REPLAY_PILOT_PREFIX','PASS_BOUNDED_FULL_REPLAY_PREFIX')
    runner=runner.replace('PASS_COMPLETE_REPLAY_PILOT','PASS_COMPLETE_FULL_REPLAY_MODULES')
    runner=once(runner,
        "assert sha(planpath)==prep['full_plan_sha256']",
        "assert prep['status']=='PREPARED_FULL_SHARED_CORE_REPLAY_UNCHECKED'\n"
        "assert sha(planpath)==prep['full_plan_sha256']\n"
        "assert len(plan['module_order'])==137\n"
        "assert not (H/'data/replay-batch-v2.lock').exists(), 'Wait for the pilot driver to finish'\n"
        "for p,d in prep['input_pins'].items():assert sha(R/p)==d,p")
    runner=once(runner,"    if not rp.exists():return None",
        "    if not rp.exists():\n"
        "        assert m not in prep['reused_pilot_receipts'], 'An accepted pilot receipt is missing; inspect it instead of recompiling'\n"
        "        return None")
    runner=once(runner,"    assert j['checker_sha256']==sha(H/'scripts/check_full_replay.py')",
        "    if m in prep['reused_pilot_receipts']:\n"
        "        previous=prep['reused_pilot_receipts'][m]\n"
        "        assert sha(rp)==previous['receipt_sha256'] and j['checker_sha256']==previous['checker_sha256']\n"
        "    else:\n"
        "        assert j['checker_sha256']==sha(H/'scripts/check_full_replay.py')")
    runner=runner.replace('14-bit checker, full initial-tree bridge and bounded prefix/checkpoint. The full contradiction and actual-snake theorem remain separate.',
        'Complete shared153 core contradiction, reusing the34 accepted pilot modules. Actual-snake composition remains separate.')
    assert "prep['pilot_plan_sha256']" not in runner
    return {'scripts/check_full_replay.py':checker,
            'scripts/run_full_replay.py':runner,
            'scripts/finish_full_replay.py':AUDITOR}


AUDITOR=r'''"""Audit every saved module of the full shared share17 contradiction."""
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
'''


def main():
    parser=argparse.ArgumentParser();parser.add_argument('--check-source-only',action='store_true');args=parser.parse_args()
    generated=texts()
    for name,source in generated.items():ast.parse(source,filename=name)
    # Validate the mixed-receipt acceptance and full-plan selection in memory.
    assert "prep['pilot_plan_sha256']" not in generated['scripts/check_full_replay.py']
    assert "prep['pilot_plan_sha256']" not in generated['scripts/run_full_replay.py']
    assert 'data/full-replay-progress.json' in generated['scripts/run_full_replay.py']
    assert 'data/full-replay-batch.lock' in generated['scripts/run_full_replay.py']
    assert "prep['reused_pilot_receipts']" in generated['scripts/check_full_replay.py']
    assert "prep['reused_pilot_receipts']" in generated['scripts/run_full_replay.py']
    required=[H/'data/pilot-completion-v2.json',H/'data/full-source-plan.json']
    missing=[path.relative_to(H).as_posix() for path in required if not path.exists()]
    if args.check_source_only:
        print(json.dumps(dict(status='PASS_FULL_RUNNER_SOURCE_SYNTAX_ONLY',Lean_started=False,
            generated_files_written=False,missing_prerequisites=missing,
            future_script_bytes={name:len(source.encode('utf-8')) for name,source in generated.items()},
            future_script_sha256={name:hashlib.sha256(source.encode('utf-8')).hexdigest() for name,source in generated.items()},
            no_pilot_recompilation_guard=True,old_pilot_checker_receipts_preserved=True,
            expected_full_modules=137,expected_axiom_reports=407)))
        return
    if missing:
        print(json.dumps(dict(status='WAITING_FOR_ACCEPTED_PILOT_AND_FULL_SOURCES',missing=missing)))
        raise SystemExit(2)
    assert not (H/'data/replay-batch-v2.lock').exists(), 'Pilot driver must finish first'
    subprocess.run([sys.executable,'-B','-X','utf8',str(H/'scripts/finish_pilot_v2.py'),'--verify-only'],cwd=R,check=True)
    pilot=read(required[0]);full=read(required[1]);old=read(H/'data/preparation-v2.json')
    pilot_plan=read(H/'data/pilot-source-plan.json')
    assert pilot['status']=='PASS_14BIT_INITIAL_TREE_AND_CHECKPOINT_PILOT' and pilot['checked_modules']==34
    assert full['status']=='SOURCE_PREPARED_UNCHECKED' and full['mode']=='full'
    assert full['module_count']==len(full['module_order'])==137
    assert full['module_order'][:34]==pilot_plan['module_order']
    assert full['cnf_dependency']=='LocalWindowCnf.ShareWindow153'
    assert full['cnf_namespace']=='Snake9.LocalWindow.ShareWindow153'
    assert full['generator_sha256']==sha(H/'scripts/emit_full_v2.py')
    assert (full['full_segments'],full['full_checkpoint_groups'],full['initial_subtrees'])==(290,10,93)
    artifacts={row['module']:row for row in full['artifacts']}
    assert len(artifacts)==137 and sum((H/row['path']).read_text(encoding='utf-8').count('#print axioms') for row in full['artifacts'])==407
    for row in full['artifacts']:
        assert sha(H/row['path'])==row['sha256'] and (H/row['path']).stat().st_size==row['bytes'],row['path']
    for row in pilot_plan['artifacts']:assert row==artifacts[row['module']],row['module']
    reused={}
    for row in pilot['receipts']:
        receipt_path=H/row['receipt'];receipt=read(receipt_path)
        assert sha(receipt_path)==row['sha256']
        assert receipt['checker_sha256']==old['execution_scripts_sha256']['scripts/check_replay_v2.py']
        reused[row['module']]=dict(receipt_sha256=sha(receipt_path),checker_sha256=receipt['checker_sha256'])
    assert list(reused)==pilot_plan['module_order']
    prep=copy.deepcopy(old)
    prep['status']='PREPARED_FULL_SHARED_CORE_REPLAY_UNCHECKED'
    prep.pop('pilot_plan_sha256')
    prep['full_plan_sha256']=sha(required[1])
    prep['accepted_pilot_sha256']=sha(required[0])
    prep['pilot_preparation_sha256']=sha(H/'data/preparation-v2.json')
    prep['pilot_module_order']=pilot_plan['module_order']
    prep['reused_pilot_receipts']=reused
    prep['execution_scripts_sha256']={name:hashlib.sha256(source.encode('utf-8')).hexdigest() for name,source in generated.items()}
    prep['preparation_script_sha256']=sha(Path(__file__))
    prep['input_pins'].update(pilot['source_files_sha256'])
    for path in [Path(__file__),*required,H/'data/preparation-v2.json',H/'data/pilot-source-plan.json',
                 H/'scripts/emit_full_v2.py',H/'scripts/finish_pilot_v2.py']:
        prep['input_pins'][path.relative_to(R).as_posix()]=sha(path)
    prep['progress_file']='data/full-replay-progress.json'
    prep['lock_file']='data/full-replay-batch.lock'
    prep['full_completion_file']='data/full-replay-completion.json'
    prep['full_modules']=137;prep['new_modules']=103;prep['expected_axiom_reports']=407
    prep['checked_modules']=34;prep['new_modules_checked']=0
    prep['scope']='Prepared complete shared-core replay, reusing34 accepted pilot modules. No new Lean module is checked by this preparation. Actual-snake composition remains separate.'
    outputs={H/name:source.encode('utf-8') for name,source in generated.items()}
    outputs[H/'data/full-execution-preparation.json']=(json.dumps(prep,indent=2)+'\n').encode('utf-8')
    for path,raw in outputs.items():
        if path.exists():assert path.read_bytes()==raw,path
    for path,raw in outputs.items():
        if not path.exists():path.write_bytes(raw)
    print(json.dumps(dict(status=prep['status'],Lean_started=False,full_modules=137,
        reused_pilot_modules=34,new_modules=103,preparation_sha256=sha(H/'data/full-execution-preparation.json'))))


if __name__=='__main__':main()
