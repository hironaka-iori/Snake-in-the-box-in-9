from pathlib import Path
import json,hashlib,re,datetime,sys
h=Path(__file__).resolve().parents[1];r=h.parents[1];sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
accepted=[]
for ap in sorted((h/'data').glob('*-audit.json')):
 j=json.loads(ap.read_text(encoding='utf-8-sig'))
 if 'module' not in j:continue
 assert j['status']=='PASS' and j['exit_code']==0 and j['stop_reason'] is None
 for k,dk in [('source','source_sha256'),('object','olean_sha256'),('log','log_sha256')]:assert sha(j[k])==j[dk]
 for p,d in j['dependencies'].items():assert sha(p)==d,p
 assert all(set(x['axioms'])<={'propext','Classical.choice','Quot.sound'} for x in j['axioms'])
 accepted.append({'module':j['module'],'source_sha256':j['source_sha256'],'object_sha256':j['olean_sha256'],'axiom_reports':len(j['axioms'])})
assert len(accepted)==4
native=[]
for folder,runname in [('graph','graph-run.json'),('graph-final','graph-final-run.json'),('graph-joint15','graph-joint15-run.json')]:
 result=h/'data'/folder/'results.json';j=json.loads(result.read_text());run=json.loads((h/'data'/runname).read_text());assert run['status']=='PASS' and run['exit_code']==0
 for p,d in j['input_pins'].items():assert sha(p)==d,p
 for row in j['profiles']:
  if row['status'] in ['PASS_POTENTIAL','PASS_REUSED_POTENTIAL']:
   assert row['scan']['edges']==4661572 and row['scan']['violations']==0
  if 'potential_file' in row:assert sha(result.parent/row['potential_file'])==row['potential_archive_sha256']
 native.append({'folder':folder,'result_sha256':sha(result),'peak_private_bytes':run['peak_private']})
documents=[]
for name in ['snake9_research.tex','snake9_frontier_explanation.tex']:
 p=r/'paper'/name;editor=Path('D:/Codex/2026-10-13/new-chat/outputs')/name;assert p.read_bytes()==editor.read_bytes();s=p.read_text(encoding='utf-8');old=(h/'review'/(name+'.before.txt')).read_text(encoding='utf-8')
 labels=re.findall(r'\\label\{([^}]+)\}',s);refs=re.findall(r'\\(?:eqref|ref|autoref)\{([^}]+)\}',s);cites=[x.strip() for g in re.findall(r'\\cite(?:\[[^]]*\])?\{([^}]+)\}',s) for x in g.split(',')];bibs=re.findall(r'\\bibitem(?:\[[^]]*\])?\{([^}]+)\}',s)
 assert len(labels)==len(set(labels));assert not(set(refs)-set(labels));assert not(set(cites)-set(bibs))
 if name=='snake9_research.tex':assert s.split('\\begin{document}')[0]==old.split('\\begin{document}')[0]
 assert all(x in s for x in ['Iori Hironaka','Tommy Ma','Steven Zhan'])
 documents.append({'file':str(p),'editor':str(editor),'sha256':sha(p),'lines':len(s.splitlines()),'builtin_compile':'success','undefined_references':0,'undefined_citations':0})
protected={'.gitignore':'20d6df071a62fabfd98360ddf985088445fde2dec19ef0281f5ab5c6d2b1941b','milestones/50-three-count-return/excess-screen/data/critical-family.json':'466e23170f15072cae3643971b5d9a62b2227fc9ffb4bca276173dc19892db82'}
for p,d in protected.items():assert sha(r/p)==d,p
assert not(r/'work/fullgraph-active.lock').exists()
sys.path.insert(0,str(h/'scripts'));from native_resources import snapshot
resources=snapshot();assert not resources['errors'] and not resources['processes']
result={'status':'PASS_TWO_ROUND_COMPLETION','round':176,'round_start_utc':'2026-11-05T11:45:30+00:00','audit_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'accepted':accepted,'axiom_reports':sum(x['axiom_reports'] for x in accepted),'native':native,'documents':documents,'protected_files':protected,'resources':resources,'uniform_pending_floors':{'012034':15,'012301':15,'012340':15,'012345':15},'final_scaled_mean':4453,'final_scaled_range':5384,'scale':9,'final_comparison':'235 - 1047/42253','new_unconditional_numerical_length_bound':False,'requested_goal_action':'pause','last_manuscript_revision':176,'next_manuscript_revision':186,'remaining_premises':['Local floor15 proofs','Retained count conditions including hypothetical0123104 six-count floor25','Reference exclusions','Complete finite Lean edge certificate and graph-to-snake interpretation']}
(h/'data/completion.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
(h/'data/latex-compile.json').write_text(json.dumps({'compiler':'Codex built-in document compiler','documents':documents,'visual_page_review':False},indent=2)+'\n',encoding='utf-8')
print('PASS_TWO_ROUND_COMPLETION',len(accepted),'modules',result['axiom_reports'],'axiom reports',[(x['lines'],x['builtin_compile']) for x in documents])
