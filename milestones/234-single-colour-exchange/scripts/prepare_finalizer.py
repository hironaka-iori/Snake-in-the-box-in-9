from pathlib import Path
H=Path(__file__).resolve().parents[1]
old=(H.parent/'233-parity-lift-construction/scripts/finalize.py').read_text(encoding='utf-8')
prefix=old[:old.index("q=read(H/'data/lift.json')")]
documents=old[old.index('docs={}'):old.index("previous=read(R/")]
body='''survey=read(H/'data/exchange.json')
assert survey['status']=='COMPLETE_STATIC_COVER' and survey['descriptions']==2227200 and survey['arguments']['start_core']==0
audit=read(H/'data/exchange-audit.json')
assert audit['status']=='PASS_FULL_INDEPENDENT_STATIC_DECISION_AUDIT' and audit['verified_descriptions']==2227200
assert all(sha(p)==v for p,v in audit['pins'].items())
assert sha(H/'scripts/audit_exchange.py')==audit['auditor_sha256']
cover=read(H/'data/final-cover-audit.json')
assert cover['status']=='PASS_COMPLETE_CANDIDATE_UNION_COVER' and cover['all_native_models_verified']==793
assert cover['elementary_certified_classes']==1244 and cover['essential_native_classes']==81
assert not cover['unresolved_candidate_classes'] and all(sha(p)==v for p,v in cover['input_pins'].items())
native=[]
for tag,result in [('exchange','exchange'),('hamilton','hamilton'),('forced-cycles','forced-cycles'),('hamilton-resume','hamilton-resume'),('exchange-audit-verified','exchange-audit')]:
    e=read(H/'data'/(tag+'-execution.json'))
    assert e['status']=='ACCEPTED_NATIVE_RESULT' and e['exit_code']==0 and e['stop_reason'] is None
    assert all(sha(p)==v for p,v in e['pins'].items()) and sha(H/'data'/(result+'.json'))==e['result_sha256']
    native.append(dict(tag=tag,receipt_sha256=sha(H/'data'/(tag+'-execution.json')),result_sha256=e['result_sha256']))
proofs=[]
for module,count in [('ColourExchange234',4)]:
    a=read(H/'data'/(module+'-audit.json'))
    assert a['status']=='PASS' and a['exit_code']==0 and a['stop_reason'] is None and len(a['axioms'])==count
    for pk,hk in [('source','source_sha256'),('object','olean_sha256'),('log','log_sha256')]:assert sha(a[pk])==a[hk]
    assert all(sha(p)==v for p,v in a['dependencies'].items())
    assert all(set(x['axioms'])<={'propext','Classical.choice','Quot.sound'} for x in a['axioms'])
    proofs.append(dict(module=module,reports=count,receipt_sha256=sha(H/'data'/(module+'-audit.json'))))
archive=read(H/'data/model-archive.json');assert len(archive['files'])==793
assert sha(H/'data'/archive['archive'])==archive['archive_sha256']
assert all(sha(H/'data'/p)==v['sha256'] for p,v in archive['files'].items())
'''
end='''previous=read(R/'milestones/233-parity-lift-construction/data/completion.json')
for x in previous['frozen_parent_search_states'].values():assert sha(R/x['path'])==x['sha256']
git=['git','-c','core.commitGraph=false','-c','maintenance.auto=false','-c','gc.auto=0']
contributor=subprocess.check_output(git+['rev-parse','origin/research/unconditional-241'],cwd=R,text=True).strip()
completion=dict(round=234,status='PROGRESS',goal_status='ACTIVE',pause_request=None,started_utc='2026-11-17 11:39:11 UTC',finished_utc=datetime.now(timezone.utc).isoformat(),interval=[191,233],new_q9_record=False,new_global_bound=False,complete_exchange_descriptions=2227200,distinct_candidate_classes=1325,elementary_certified_classes=1244,essential_native_classes=81,native_models_verified=793,unresolved_candidate_classes=[],maximum_seed_overlap_for_192=189,minimum_old_vertices_omitted=3,minimum_new_vertices_added=4,restricted_one_complete_96_class_at_most_one_exchange_optimum=191,finite_cover_lean_certified=False,native_runs=native,proofs=proofs,static_audit_sha256=sha(H/'data/exchange-audit.json'),final_cover_audit_sha256=sha(H/'data/final-cover-audit.json'),documents=docs,contributor_revision=contributor,contributor_231_completed=False,independent_233_rebuild=False,full_manuscript_review_round=230,next_full_manuscript_review_round=240,next_construction='Two minority replacements with a joint optional-vertex circuit; proposed, not run',frozen_parent_search_states=previous['frozen_parent_search_states'])
save(H/'data/completion.json',completion)
save(H/'data/document-verification.json',dict(documents=docs,scope='Preserved authors, hypersetup, labels and citations; exact mirrors; bounded source review and successful built-in compilation. No full PDF visual review.'))
handoff=(H/'HANDOFF.md').read_text(encoding='utf-8')
for name in ['CURRENT_STATUS.md','NEXT_AGENT_PROMPT.md']:(R/'handoff'/name).write_text(handoff,encoding='utf-8',newline='\\n')
old=(R/'README.md').read_text(encoding='utf-8')
assert not old.startswith('# Current result after round 234')
(R/'README.md').write_text((H/'README_CHECKPOINT.md').read_text(encoding='utf-8')+'\\n'+old,encoding='utf-8',newline='\\n')
print('FINALIZED_ROUND234; GOAL_ACTIVE')
'''
(H/'scripts/finalize.py').write_text(prefix+body+documents+end,encoding='utf-8',newline='\n')
print('PREPARED_FINALIZER234')
