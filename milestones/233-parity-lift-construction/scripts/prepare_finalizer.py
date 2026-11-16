from pathlib import Path
H=Path(__file__).resolve().parents[1]
old=(H.parent/'232-minority-contraction/scripts/finalize.py').read_text(encoding='utf-8')
prefix=old[:old.index("q=read(H/'data/minority.json')")]
documents=old[old.index('docs={}'):old.index("previous=read(R/")]
body='''q=read(H/'data/lift.json')
assert q['status']=='COMPLETE_QUERY_BATCH' and len(q['results'])==6763 and q['q9_witness'] is None
assert q['statuses']==dict(TOO_MANY_LEAVES=27,ISOLATED=6698,WITNESS=28,INFEASIBLE=8,DISCONNECTED=2)
e=read(H/'data/lift-execution.json')
assert e['status']=='ACCEPTED_NATIVE_RESULT' and e['exit_code']==0 and e['stop_reason'] is None
assert all(sha(p)==v for p,v in e['pins'].items()) and sha(H/'data/lift.json')==e['result_sha256']
audit=read(H/'data/lift-audit.json')
assert audit['status']=='PASS_INDEPENDENT_SAVED_LIFT_AUDIT' and audit['rows']==6763
assert len(audit['verified_models'])==36 and len(audit['verified_witnesses'])==28
assert sha(H/'scripts/audit_lift.py')==audit['auditor_sha256']
assert all(sha(p)==v for p,v in audit['pins'].items())
proofs=[]
for module,count in [('ParityLift233',4),('IsolationDeletion233',2)]:
    a=read(H/'data'/(module+'-audit.json'))
    assert a['status']=='PASS' and a['exit_code']==0 and a['stop_reason'] is None and len(a['axioms'])==count
    for pk,hk in [('source','source_sha256'),('object','olean_sha256'),('log','log_sha256')]:assert sha(a[pk])==a[hk]
    assert all(sha(p)==v for p,v in a['dependencies'].items())
    assert all(set(x['axioms'])<={'propext','Classical.choice','Quot.sound'} for x in a['axioms'])
    proofs.append(dict(module=module,reports=count,receipt_sha256=sha(H/'data'/(module+'-audit.json'))))
archive=read(H/'data/model-archive.json');assert len(archive['files'])==36
assert sha(H/'data'/archive['archive'])==archive['archive_sha256']
assert all(sha(H/'data'/p)==v['sha256'] for p,v in archive['files'].items())
'''
end='''previous=read(R/'milestones/232-minority-contraction/data/completion.json')
for x in previous['frozen_parent_search_states'].values():assert sha(R/x['path'])==x['sha256']
git=['git','-c','core.commitGraph=false','-c','maintenance.auto=false','-c','gc.auto=0']
contributor=subprocess.check_output(git+['rev-parse','origin/research/unconditional-241'],cwd=R,text=True).strip()
completion=dict(round=233,status='PROGRESS',goal_status='PAUSE_REQUESTED_AFTER_PUBLICATION',pause_after_round=233,started_utc='2026-11-16 14:03:02 UTC',finished_utc=datetime.now(timezone.utc).isoformat(),interval=[191,233],new_q9_record=False,new_global_bound=False,universal_projection_criterion='written, supported by accepted general constructors',complete_lift_cases=6763,isolated_cases=6698,excess_leaf_cases=27,disconnected_cases=2,native_infeasible_cases=8,shorter_q6_witnesses=28,necessary_deletions={'saved_Q6_parent':3,'saved_Q7_parent':4,'saved_Q8_parent':5},restricted_deletion_lift_ceilings={'saved_Q6_parent':46,'saved_Q7_parent':92,'saved_Q8_parent':186},restricted_ceilings_attained=False,native_result_sha256=sha(H/'data/lift.json'),native_receipt_sha256=sha(H/'data/lift-execution.json'),independent_audit_sha256=sha(H/'data/lift-audit.json'),proofs=proofs,solver_exclusions_lean_certified=False,whole_cube_and_counting_bridges='written',documents=docs,contributor_revision=contributor,contributor_231_completed=False,independent_233_rebuild=False,full_manuscript_review_round=230,next_full_manuscript_review_round=240,frozen_parent_search_states=previous['frozen_parent_search_states'])
save(H/'data/completion.json',completion)
save(H/'data/document-verification.json',dict(documents=docs,scope='Preserved authors, hypersetup and labels; exact mirrors; bounded source review and successful built-in compilation. No full PDF visual review.'))
handoff=(H/'HANDOFF.md').read_text(encoding='utf-8')
for name in ['CURRENT_STATUS.md','NEXT_AGENT_PROMPT.md']:(R/'handoff'/name).write_text(handoff,encoding='utf-8',newline='\\n')
old=(R/'README.md').read_text(encoding='utf-8')
assert not old.startswith('# Current result after round 233')
header=(H/'README_CHECKPOINT.md').read_text(encoding='utf-8')
(R/'README.md').write_text(header+'\\n'+old,encoding='utf-8',newline='\\n')
print('FINALIZED_ROUND233; PAUSE_AFTER_PUBLICATION')
'''
(H/'scripts/finalize.py').write_text(prefix+body+documents+end,encoding='utf-8',newline='\n')
print('PREPARED_FINALIZER233')
