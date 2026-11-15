from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,re,subprocess
H=Path(__file__).resolve().parents[1];R=H.parents[1];D=Path('D:/Codex/2026-10-13/new-chat/outputs')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):return json.loads(Path(p).read_bytes())
def save(p,x):Path(p).write_text(json.dumps(x,indent=2)+'\n',encoding='utf-8',newline='\n')
assert not (H/'data/forest-search.lock').exists()
proofs=[]
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
docs={}
for name,receipt in [('snake9_frontier_explanation.tex','frontier-compile-final.json'),('snake9_research.tex','main-compile-final.json')]:
 p=D/name;assert p.read_bytes()==(R/'paper'/name).read_bytes()
 before=(H/'data'/('before-'+name)).read_text(encoding='utf-8');after=p.read_text(encoding='utf-8')
 assert re.search(r'\\author\{[^\n]*',before).group()==re.search(r'\\author\{[^\n]*',after).group()
 if name=='snake9_research.tex':assert re.search(r'\\hypersetup\{.*?\n\}',before,re.S).group()==re.search(r'\\hypersetup\{.*?\n\}',after,re.S).group()
 assert set(re.findall(r'\\label\{([^}]+)\}',before))<=set(re.findall(r'\\label\{([^}]+)\}',after))
 labels=re.findall(r'\\label\{([^}]+)\}',after);assert len(labels)==len(set(labels))
 assert set(re.findall(r'\\(?:ref|eqref|pageref)\{([^}]+)\}',after))<=set(labels)
 bib=set(re.findall(r'\\bibitem\{([^}]+)\}',after))
 assert {v.strip() for g in re.findall(r'\\cite\{([^}]+)\}',after) for v in g.split(',')}<=bib
 c=read(H/'data'/receipt);assert not c.get('isError',False)
 assert any(json.loads(t['text']).get('kind')=='success' for t in c['content'] if t['type']=='text')
 docs[name]={'editor':str(p),'mirror':str(R/'paper'/name),'sha256':sha(p),'compile_receipt':receipt,'compile_sha256':sha(H/'data'/receipt),'lines':len(after.splitlines())}
save(H/'data/document-verification.json',{'scope':'Bounded revision review, exact mirrors, preserved authors/settings and successful compilation. No page-by-page PDF visual audit.','documents':docs})
review=(H/'logs/review-final-documents.md').read_text(encoding='utf-8');assert all(d['sha256'] in review for d in docs.values())
frozen=read(H.parent/'221-square-parity/data/completion.json')['frozen_parent_search_states']
for v in frozen.values():assert sha(R/v['path'])==v['sha256']
intent=read(H/'data/round-intent.json');next_step=(H/'data/next-step.txt').read_text(encoding='utf-8').strip()
contributor=subprocess.check_output(['git','-c','core.commitGraph=false','-c','maintenance.auto=false','-c','gc.auto=0','rev-parse','origin/research/unconditional-241'],cwd=R,text=True).strip()
assert contributor==intent['contributor_at_start']
ledger=read(H/'data/deep-ledger.json')
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
save(H/'data/completion.json',completion)
handoff=(H/'data/handoff.txt').read_text(encoding='utf-8').rstrip()+'\n\nNext step: '+next_step+'\n'
for name in ['CURRENT_STATUS.md','NEXT_AGENT_PROMPT.md']:(R/'handoff'/name).write_text(handoff,encoding='utf-8',newline='\n')
header=(H/'data/readme-header.txt').read_text(encoding='utf-8').rstrip();old=(R/'README.md').read_text(encoding='utf-8');assert not old.startswith('# Current result after round 222')
(R/'README.md').write_text(header+'\n\n'+old,encoding='utf-8',newline='\n')
print('FROZEN_ROUND222; PAUSE_AFTER_PUBLICATION; FIXED_PARENT_ROUTE_CLOSED')
