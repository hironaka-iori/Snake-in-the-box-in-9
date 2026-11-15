from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,re
H=Path(__file__).resolve().parents[1];R=H.parents[1];D=Path('D:/Codex/2026-10-13/new-chat/outputs')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):return json.loads(Path(p).read_bytes())
def save(p,x):Path(p).write_text(json.dumps(x,indent=2)+'\n',encoding='utf-8',newline='\n')
assert not (H/'data/forest-search.lock').exists()
proofs=[]
for name,count in [('Forest220',4),('SquareParity220',3)]:
 p=H/'data'/(name+'-audit.json');a=read(p)
 assert a['status']=='PASS' and a['exit_code']==0 and a['stop_reason'] is None
 for pk,hk in [('source','source_sha256'),('object','olean_sha256'),('log','log_sha256')]:assert sha(a[pk])==a[hk]
 for path,digest in a['dependencies'].items():assert sha(path)==digest
 assert len(a['axioms'])==count and all(set(q['axioms'])<={'propext','Classical.choice','Quot.sound'} for q in a['axioms'])
 proofs.append({'module':name,'receipt':str(p.relative_to(R)),'sha256':sha(p),'reports':count})
audits={}
for name,status in [('forest','PASS_EXACT_SUBSET_ROWS_UPPERS_PRIMALS_CYCLES_FLOWS_AND_TARGET94'),('parity','PASS_EXACT_SHORT_CYCLE_PARITY_AUDIT')]:
 p=H/'data'/(name+'-audit.json');a=read(p);assert a['status']==status
 for path,digest in a['pins'].items():assert sha(H/path)==digest,path
 audits[name]=sha(p)
docs={}
for name,receipt in [('snake9_frontier_explanation.tex','frontier-compile.json'),('snake9_research.tex','main-compile.json')]:
 p=D/name;assert p.read_bytes()==(R/'paper'/name).read_bytes()
 before=(H/'data'/('before-'+name)).read_text(encoding='utf-8');after=p.read_text(encoding='utf-8')
 assert re.search(r'\\author\{[^\n]*',before).group()==re.search(r'\\author\{[^\n]*',after).group()
 if name=='snake9_research.tex':
  assert re.search(r'\\hypersetup\{.*?\n\}',before,re.S).group()==re.search(r'\\hypersetup\{.*?\n\}',after,re.S).group()
  assert set(re.findall(r'\\label\{([^}]+)\}',before))<=set(re.findall(r'\\label\{([^}]+)\}',after))
 labels=re.findall(r'\\label\{([^}]+)\}',after);assert len(labels)==len(set(labels))
 assert set(re.findall(r'\\(?:ref|eqref|pageref)\{([^}]+)\}',after))<=set(labels)
 bib=set(re.findall(r'\\bibitem\{([^}]+)\}',after))
 assert {v.strip() for g in re.findall(r'\\cite\{([^}]+)\}',after) for v in g.split(',')}<=bib
 c=read(H/'data'/receipt);assert not c.get('isError',False)
 assert any(json.loads(t['text']).get('kind')=='success' for t in c['content'] if t['type']=='text')
 docs[name]={'editor':str(p),'mirror':str(R/'paper'/name),'sha256':sha(p),'compile_receipt':receipt,'compile_sha256':sha(H/'data'/receipt),'lines':len(after.splitlines())}
save(H/'data/document-verification.json',{'scope':'Full source and final revision reviews, exact mirrors, preserved authors/settings and compilation success. No page-by-page PDF visual audit.','documents':docs})
reviews={name:sha(H/'logs'/name) for name in ['review-upper-paper.md','review-construction-paper.md','review-frontier.md','review-final-documents.md','forest-proof-review.md','forest-audit-review.md','parity-review.md']}
review=(H/'logs/review-final-documents.md').read_text(encoding='utf-8');assert all(d['sha256'] in review for d in docs.values())
frozen=read(H.parent/'219-linear-partner/data/completion.json')['frozen_parent_search_states']
for v in frozen.values():assert sha(R/v['path'])==v['sha256']
intent=read(H/'data/round-intent.json');next_step=(H/'data/next-step.txt').read_text(encoding='utf-8').strip()
completion={'round':220,'status':'PROGRESS','previous_goal_turn':'PROGRESS','started_utc':intent['started_utc'],'utc':datetime.now(timezone.utc).isoformat(),'goal_state':'ACTIVE','pause_policy':intent['pause_policy'],'email_sent':False,'email_limitation':'No sending connection available.','interval':[191,233],'contributor_revision':intent['contributor_at_start'],'contributor_changed':False,'independent_233_rebuild':False,'new_q9_record':False,'new_global_bound':False,'fixed_parent_97_edge_exclusions_with_exact_weights':True,'fixed_parent_one_crossing_ceiling':195,'exact_target94_both_roots':True,'all_cycle_and_forest_barrier':True,'parity_strengthened_lp_solved':False,'accepted_new_modules':2,'theorem_reports':7,'proofs':proofs,'audit_hashes':audits,'forest_summary':read(H/'data/forest-summary.json'),'rational_summary':read(H/'data/rational-summary.json'),'flow_summary':read(H/'data/flow-summary.json'),'frozen_parent_search_states':frozen,'six_coordinate_unresolved':27,'software_tests_created_or_run':False,'compile_success':True,'full_paper_review':{'before_main_lines':10979,'before_frontier_lines':620,'reports':reviews,'next_scheduled_round':230},'scope':'Generic Lean results and independent exact numerical audits; concrete array assembly remains separate.','next_step':next_step}
save(H/'data/completion.json',completion)
handoff=(H/'data/handoff.txt').read_text(encoding='utf-8')+'\n\nNext step: '+next_step+'\n'
for name in ['CURRENT_STATUS.md','NEXT_AGENT_PROMPT.md']:(R/'handoff'/name).write_text(handoff,encoding='utf-8',newline='\n')
header=(H/'data/readme-header.txt').read_text(encoding='utf-8');old=(R/'README.md').read_text(encoding='utf-8');assert not old.startswith('# Current result after round 220')
(R/'README.md').write_text(header+'\n'+old,encoding='utf-8',newline='\n')
print('FROZEN_ROUND220; ACTIVE; SQUARE_PARITY_ROWS_NEXT')
