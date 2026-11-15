from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,re,subprocess
H=Path(__file__).resolve().parents[1];R=H.parents[1];D=Path('D:/Codex/2026-10-13/new-chat/outputs')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):return json.loads(Path(p).read_bytes())
def save(p,x):Path(p).write_text(json.dumps(x,indent=2)+'\n',encoding='utf-8',newline='\n')
assert not (H/'data/forest-search.lock').exists()
p=H/'data/CutParity221-audit.json';a=read(p)
assert a['status']=='PASS' and a['exit_code']==0 and a['stop_reason'] is None
for pk,hk in [('source','source_sha256'),('object','olean_sha256'),('log','log_sha256')]:assert sha(a[pk])==a[hk]
for path,digest in a['dependencies'].items():assert sha(path)==digest
assert len(a['axioms'])==2 and all(set(q['axioms'])<={'propext','Classical.choice','Quot.sound'} for q in a['axioms'])
proofs=[{'module':'CutParity221','receipt':str(p.relative_to(R)),'sha256':sha(p),'reports':2}]
audits={}
for name,status in [
 ('square','PASS_EXACT_SQUARE_SUBSET_ROWS_AND_UPPER_CERTIFICATES'),
 ('rational','PASS_EXACT_SQUARE_MODEL_PRIMALS_AND_OCCUPANCY_CYCLE_POTENTIALS'),
 ('long','PASS_EXACT_LONG_CYCLE_ROWS_AND_UPPER_CERTIFICATES'),
 ('long-primal','PASS_EXACT_LONG_PRIMALS_ALL_THREE_FAMILIES_AND_TARGET94'),
 ('first','PASS_EXACT_FIRST_STEP_COVERAGE_AND_UPPER_CERTIFICATES')]:
 p=H/'data'/(name+'-audit.json');a=read(p);assert a['status']==status
 for path,digest in a.get('pins',{}).items():assert sha(H/path)==digest,path
 for row in a.get('models',[]):
  for path,digest in row.get('pins',{}).items():
   resolved=H/path
   if name=='rational':resolved=H/'data'/f"{'square' if path=='model.json' else 'rational'}-{row['root']}"/path
   assert sha(resolved)==digest,path
 if name=='first':
  for row in a['branches']:assert sha(H/row['file'])==row['sha256']
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
frozen=read(H.parent/'220-subset-forest/data/completion.json')['frozen_parent_search_states']
for v in frozen.values():assert sha(R/v['path'])==v['sha256']
intent=read(H/'data/round-intent.json');next_step=(H/'data/next-step.txt').read_text(encoding='utf-8').strip()
contributor=subprocess.check_output(['git','-c','core.commitGraph=false','-c','maintenance.auto=false','-c','gc.auto=0','rev-parse','origin/research/unconditional-241'],cwd=R,text=True).strip()
assert contributor==intent['contributor_at_start']
completion={'round':221,'status':'PROGRESS','previous_goal_turn':'PROGRESS','started_utc':intent['started_utc'],'utc':datetime.now(timezone.utc).isoformat(),'goal_state':'ACTIVE','pause_policy':'Continue; user authorizes a pause for an exceptional result or prolonged stagnation in her work and this investigation. Contributor work alone cannot trigger a pause. No trigger this round.','email_sent':False,'email_limitation':'No sending connection available.','interval':[191,233],'contributor_revision':contributor,'contributor_changed':False,'independent_233_rebuild':False,'new_q9_record':False,'new_global_bound':False,'fixed_parent_95_edge_exclusions_with_exact_weights':True,'fixed_parent_one_crossing_ceiling':193,'exact_target94_both_roots':True,'complete_occupancy_forest_and_parity_barrier':True,'first_step_branches':14,'excluded_first_step_branches':[[0,16],[78,14],[78,74]],'unresolved_first_step_branches':11,'accepted_new_modules':1,'theorem_reports':2,'proofs':proofs,'audit_hashes':audits,'long_summary':read(H/'data/long-summary.json'),'first_summary':read(H/'data/first-summary.json'),'frozen_parent_search_states':frozen,'six_coordinate_unresolved':27,'software_tests_created_or_run':False,'compile_success':True,'document_review_sha256':sha(H/'logs/review-final-documents.md'),'next_full_paper_review':230,'scope':'Generic Lean results and independent exact numerical audits; end-to-end Lean assembly of concrete arrays remains separate.','next_step':next_step}
save(H/'data/completion.json',completion)
handoff=(H/'data/handoff.txt').read_text(encoding='utf-8').rstrip()+'\n\nNext step: '+next_step+'\n'
for name in ['CURRENT_STATUS.md','NEXT_AGENT_PROMPT.md']:(R/'handoff'/name).write_text(handoff,encoding='utf-8',newline='\n')
header=(H/'data/readme-header.txt').read_text(encoding='utf-8').rstrip();old=(R/'README.md').read_text(encoding='utf-8');assert not old.startswith('# Current result after round 221')
(R/'README.md').write_text(header+'\n\n'+old,encoding='utf-8',newline='\n')
print('FROZEN_ROUND221; ACTIVE; PREFIX_BRANCHING_NEXT')
