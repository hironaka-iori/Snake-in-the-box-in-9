"""Audit the actual-snake share17 composition with its count conditions intact."""
from pathlib import Path
import argparse, hashlib, json, re

H=Path(__file__).resolve().parents[1];R=H.parents[1]
S=R/'milestones/154-share17-broader-semantics'
read=lambda p:json.loads(Path(p).read_text(encoding='utf-8-sig'))
cache={}
def sha(p):
    p=Path(p);key=(str(p.resolve()),p.stat().st_size,p.stat().st_mtime_ns)
    if key not in cache:
        digest=hashlib.sha256()
        with p.open('rb') as stream:
            for block in iter(lambda:stream.read(1048576),b''):digest.update(block)
        cache[key]=digest.hexdigest()
    return cache[key]

def checked_receipt(path, expected_source=None, expected_object=None):
    q=read(path)
    assert q['status']=='PASS' and q['exit_code']==0 and q['stop_reason'] is None,path
    if expected_source is not None:assert Path(q['source']).resolve()==Path(expected_source).resolve()
    if expected_object is not None:assert Path(q['object']).resolve()==Path(expected_object).resolve()
    assert sha(q['source'])==q['source_sha256'] and sha(q['object'])==q['olean_sha256']
    assert sha(q['log'])==q['log_sha256']
    folder=Path(q['log']).parent
    assert sha(folder/'source.lean.txt')==q['source_sha256']
    assert sha(folder/'checker.py.txt')==q['checker_sha256']
    for dependency,digest in q['dependencies'].items():assert sha(dependency)==digest,dependency
    source=Path(q['source']).read_text(encoding='utf-8')
    assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b',source)
    assert len(q['axioms'])==source.count('#print axioms')
    assert all(set(row['axioms'])<={'propext','Classical.choice','Quot.sound'} for row in q['axioms'])
    return q

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--verify-only',action='store_true');args=parser.parse_args()
    finalpath=H/'data/ShareComplete155-audit.json'
    if not finalpath.exists():
        print(json.dumps(dict(status='WAITING_FOR_ACTUAL_SNAKE_COMPOSITION')));raise SystemExit(2)
    planpath=H/'data/final-composition-plan.json';plan=read(planpath)
    assert plan['status']=='PREPARED_COUNT_CONDITIONED_ACTUAL_SNAKE_COMPOSITION'
    for p,digest in plan['script_pins'].items():assert sha(R/p)==digest,p
    for p,digest in plan['input_pins'].items():assert sha(R/p)==digest,p
    sempath=S/'data/semantics-completion.json';sem=read(sempath)
    assert sem['status']=='PASS_BROADER_CORE_SEMANTICS_AND_CONDITIONAL_ACTUAL_SNAKE_SHARE17'
    assert (sem['checked_modules'],sem['axiom_reports'],sem['shared_core_clauses'])==(98,100,11869)
    assert sem['bounds']==[[4,4],[0,4],[4,4],[0,5],[3,3]]
    assert sem['reverse_bounds']==[[3,3],[0,5],[4,4],[0,4],[4,4]]
    semantic_plan=read(S/'data/semantic-plan-v2.json');semantic_progress=read(S/'data/semantic-progress-v2.json')
    assert sha(S/'data/semantic-plan-v2.json')==sem['plan_sha256']==semantic_progress['plan_sha256']
    assert sha(S/'data/source-plan.json')==sem['source_plan_sha256']
    assert sha(S/'data/semantic-progress-v2.json')==sem['progress_sha256']
    assert [row['module'] for row in sem['receipts']]==semantic_plan['module_order']
    semantic_artifacts={row['module']:row for row in semantic_plan['artifacts']}
    for row in sem['receipts']:
        path=R/row['receipt'];assert sha(path)==row['sha256']
        q=checked_receipt(path,S/semantic_artifacts[row['module']]['path'],S/'build'/(row['module'].replace('.','/')+'.olean'))
        assert q['source_sha256']==semantic_artifacts[row['module']]['sha256']
        previous=semantic_plan['recovery_v2']['reused_receipts'].get(row['module'])
        if previous:
            assert sha(path)==previous['receipt_sha256'] and q['checker_sha256']==previous['checker_sha256']
        else:assert q['checker_sha256']==sha(S/'scripts/check_module_v2.py')
    fullpath=H/'data/full-replay-completion.json';full=read(fullpath)
    assert full['status']=='PASS_COMPLETE_SHARED_SHARE17_CORE_CONTRADICTION'
    assert (full['checked_modules'],full['axiom_reports'],full['initial_core_clauses'],full['deductions'],full['references'])==(137,407,11869,30305,1754767)
    assert full['final_theorem']=='Snake9.ReplayFull153.unsat'
    assert full['final_CNF']=='Snake9.LocalWindow.ShareWindow153.cnf'
    for p,digest in full['source_files_sha256'].items():assert sha(R/p)==digest,p
    fullplan=read(H/'data/full-source-plan.json');fullprep=read(H/'data/full-execution-preparation.json')
    assert [row['module'] for row in full['receipts']]==fullplan['module_order']
    full_artifacts={row['module']:row for row in fullplan['artifacts']}
    for row in full['receipts']:
        path=H/row['receipt'];assert sha(path)==row['sha256']
        q=checked_receipt(path,H/full_artifacts[row['module']]['path'],H/'build'/(row['module'].replace('.','/')+'.olean'))
        assert q['source_sha256']==full_artifacts[row['module']]['sha256']
        previous=fullprep['reused_pilot_receipts'].get(row['module'])
        if previous:
            assert sha(path)==previous['receipt_sha256'] and q['checker_sha256']==previous['checker_sha256']
        else:assert q['checker_sha256']==sha(H/'scripts/check_full_replay.py')
    final=checked_receipt(finalpath,H/'lean/ShareComplete155.lean',H/'build/ShareComplete155.olean')
    assert final['source_sha256']==plan['artifacts'][0]['sha256']
    assert final['checker_sha256']==sha(H/'scripts/check_final.py')
    assert len(final['axioms'])==1 and final['axioms'][0]['theorem']=='Snake9.CriticalShare155.share17'
    source=Path(final['source']).read_text(encoding='utf-8')
    signature=source[source.index('theorem share17'):source.index(':=')]
    normalized=' '.join(signature.split())
    assert normalized==plan['expected_signature']
    assert not re.search(r'\b(Unsat|hunsat|href)\b',signature)
    assert '{m : Nat} (p : Snake m) (r : Nat) (hr : r+6 ≤ m)' in normalized
    forward='coreAlpha p (r+1) = 4 ∧ coreAlpha p (r+2) ≤ 4 ∧ coreAlpha p (r+3) = 4 ∧ coreAlpha p (r+4) ≤ 5 ∧ coreAlpha p (r+5) = 3'
    reverse='coreAlpha p (r+1) = 3 ∧ coreAlpha p (r+2) ≤ 5 ∧ coreAlpha p (r+3) = 4 ∧ coreAlpha p (r+4) ≤ 4 ∧ coreAlpha p (r+5) = 4'
    assert forward in normalized and reverse in normalized
    assert '(canon (dsOf p r 6) = [0,1,2,0,3,2]' in normalized
    assert '(canon (dsOf p r 6).reverse = [0,1,2,0,3,2]' in normalized
    assert normalized.endswith('17 ≤ ((List.range 5).map fun i => coreShare 12 p (r+i+1)).sum')
    assert source.count('theorem ')==1 and source.count('#print axioms')==1
    assert 'Snake9.CriticalShare154.share17_of_core_unsat Snake9.ReplayFull153.unsat p r hr hcase' in source
    record=dict(status='PASS_ACTUAL_SNAKE_SHARE17_WITH_COUNT_CONDITIONS',
        theorem='Snake9.CriticalShare155.share17',actual_snake_composition_complete=True,
        shared_core_contradiction_complete=True,semantic_modules=98,replay_modules=137,
        directions=[0,1,2,0,3,2],bounds=sem['bounds'],reverse_bounds=sem['reverse_bounds'],
        resolution=12,share_lower_bound=17,count_conditions_retained=True,reversal_included=True,
        extra_unsat_premise=False,universal_012032_share17=False,new_global_upper_bound=False,
        final_axioms=final['axioms'],expected_signature=normalized,
        source_files_sha256={p.relative_to(R).as_posix():sha(p) for p in [Path(__file__),planpath,
            sempath,fullpath,finalpath,H/'lean/ShareComplete155.lean',H/'data/final-target.json']},
        scope='Every actual Q9 snake window satisfying one of the stated forward or reversed count conditions has five-centre share at least17. No Unsat premise remains. No statement about all012032 windows or a new global maximum is asserted.')
    target=H/'data/actual-snake-completion.json'
    if args.verify_only or target.exists():assert target.exists() and read(target)==record
    else:target.write_bytes((json.dumps(record,indent=2)+'\n').encode('utf-8'))
    print(json.dumps(record))

if __name__=='__main__':main()
