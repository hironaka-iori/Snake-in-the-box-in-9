from pathlib import Path
H=Path(__file__).resolve().parents[1];R=H.parents[1]
s=(R/'milestones/221-square-parity/scripts/finalize.py').read_text(encoding='utf-8')
start=s.index("p=H/'data/CutParity221-audit.json'");end=s.index('docs={}',start)
s=s[:start]+'''proofs=[]
for name,count in [('Prefix222',3),('PartnerIsometry222',1)]:
 p=H/'data'/(name+'-audit.json');a=read(p)
 assert a['status']=='PASS' and a['exit_code']==0 and a['stop_reason'] is None
 for pk,hk in [('source','source_sha256'),('object','olean_sha256'),('log','log_sha256')]:assert sha(a[pk])==a[hk]
 for path,digest in a['dependencies'].items():assert sha(path)==digest
 assert len(a['axioms'])==count and all(set(q['axioms'])<={'propext','Classical.choice','Quot.sound'} for q in a['axioms'])
 proofs.append({'module':name,'receipt':str(p.relative_to(R)),'sha256':sha(p),'reports':count})
audits={}
for name,status in [('prefix','PASS_EXACT_STAGE1_PREFIX_COVERAGE_AND_CERTIFICATES'),('deep','PASS_EXACT_COMPLETE_FIXED_ROOT_PREFIX_EXCLUSION')]:
 p=H/'data'/(name+'-audit.json');a=read(p);assert a['status']==status
 for path,digest in a['pins'].items():assert sha(R/path)==digest,path
 audits[name]=sha(p)
'''+s[end:]
s=s.replace("H.parent/'220-subset-forest/data/completion.json'","H.parent/'221-square-parity/data/completion.json'")
start=s.index('completion={');end=s.index("save(H/'data/completion.json'",start)
s=s[:start]+'''ledger=read(H/'data/deep-ledger.json')
assert len(ledger['nodes'])==80 and not ledger['queue']
assert sum(n['status']=='EXPANDED' for n in ledger['nodes'].values())==27
assert sum(n['status'].startswith('EXCLUDED') for n in ledger['nodes'].values())==53
assert not any(n['status'].startswith('PENDING') for n in ledger['nodes'].values())
completion={'round':222,'status':'PROGRESS','previous_goal_turn':'PROGRESS','started_utc':intent['started_utc'],'utc':datetime.now(timezone.utc).isoformat(),
 'goal_decision':'PAUSE_AFTER_PUBLICATION','pause_basis':'User-authorized pause after a substantial own-research result: complete closure of the fixed-parent one-crossing improvement route. Contributor work is not a trigger.',
 'email_sent':False,'email_limitation':'No sending connection available.','interval':[191,233],'contributor_revision':contributor,'contributor_changed':False,'independent_233_rebuild':False,
 'new_q9_record':False,'new_global_bound':False,'fixed_parent_93_edge_exclusion_both_roots':True,'arbitrary_compatible_partner_max_edges':92,
 'fixed_parent_one_crossing_ceiling':191,'same_cube_isometry_class_included':True,'restricted_ceiling_attained':False,
 'tree_nodes':80,'expanded_nodes':27,'excluded_leaves':53,'pending_leaves':0,'maximum_used_prefix_depth':6,'new_queries':77,
 'ledger_sha256':sha(H/'data/deep-ledger.json'),'largest_exact_leaf_bounds':{'0':[9396307,100000],'78':[93984077,1000000]},
 'initial_run_status':'INTERRUPTED_LOW_FREE_MEMORY','initial_completed_queries':45,'first_continuation_queries':29,'deep_continuation_queries':3,
 'accepted_new_modules':2,'theorem_reports':4,'proofs':proofs,'audit_hashes':audits,
 'review_hashes':{name:sha(H/'logs'/name) for name in ['model-validity-review.md','review-final-documents.md','prefix-proof-review.md','isometry-proof-review.md']},
 'frozen_parent_search_states':frozen,'six_coordinate_unresolved':27,'software_tests_created_or_run':False,'compile_success':True,'next_full_paper_review':230,
 'scope':'Complete exact native-arithmetic exclusion plus written actual-path interpretation and generic Lean results. End-to-end Lean numerical assembly remains separate.',
 'next_step':next_step}
'''+s[end:]
s=s.replace("'# Current result after round 221'","'# Current result after round 222'")
s=s.replace("print('FROZEN_ROUND221; ACTIVE; PREFIX_BRANCHING_NEXT')","print('FROZEN_ROUND222; PAUSE_AFTER_PUBLICATION; FIXED_PARENT_ROUTE_CLOSED')")
(H/'scripts/finalize.py').write_text(s,encoding='utf-8',newline='\n')
print('FINALIZER_PREPARED_WITH_PAUSE_DECISION')
