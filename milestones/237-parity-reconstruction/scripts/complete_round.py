from pathlib import Path
import hashlib,json,re,datetime,subprocess
H=Path(__file__).resolve().parents[1];R=H.parents[1]
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):return json.loads(Path(p).read_bytes())
checked={};proofs=[]
for p in sorted((H/'data').glob('*-audit.json')):
 d=read(p)
 if d.get('status')!='PASS' or 'module' not in d:continue
 assert d['exit_code']==0 and d['stop_reason'] is None
 for key,hkey in [('source','source_sha256'),('object','olean_sha256'),('log','log_sha256')]:
  assert sha(d[key])==d[hkey],d[key]
 for f,h in d['dependencies'].items():
  if f not in checked:checked[f]=sha(f)
  assert checked[f]==h,f
 assert 'sorryAx' not in Path(d['log']).read_text(encoding='utf-8')
 proofs.append(dict(module=d['module'],reports=len(d['axioms']),receipt_sha256=sha(p)))
for n in ['inverse','spectral','axis','example']:
 assert read(H/'data'/(n+'-replay.json'))['status']=='PASS'
assert read(H/'majority/kernel-cuts.json')['status']=='PASS'
assert read(H/'data/finite-input-audit.json')['status']=='PASS_FINITE_INPUT_AUDIT'
D=Path('D:/Codex/2026-10-13/new-chat/outputs');docs={}
for name in ['snake9_research','snake9_frontier_explanation']:
 a=D/(name+'.tex');b=R/'paper'/(name+'.tex');assert a.read_bytes()==b.read_bytes()
 c=H/'data'/(name+'-compile.json');assert json.loads(read(c)['content'][0]['text'])['kind']=='success'
 current=a.read_text(encoding='utf-8');old=subprocess.check_output(['git','show','HEAD:paper/'+name+'.tex'],cwd=R).decode('utf-8')
 for pattern in [r'\\author\{[^\n]*',r'\\hypersetup\{[^\n]*']:
  assert re.findall(pattern,current)==re.findall(pattern,old)
 labels=re.findall(r'\\label\{([^}]+)\}',current);assert len(labels)==len(set(labels))
 docs[name+'.tex']=dict(editor=str(a),mirror=str(b),sha256=sha(a),compile_sha256=sha(c))
prior=read(R/'milestones/236-parity-exchange-frontier/data/completion.json')
for item in prior['frozen_parent_search_states'].values():assert sha(R/item['path'])==item['sha256']
review=H/'logs/final-document-review.json';assert review.exists()
out=dict(round=237,status='PROGRESS',goal_status='ACTIVE_CONTINUE_THROUGH_239',pause_after_round=239,
 resumed_utc='2026-11-18 10:39:15 UTC',finished_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
 interval=[191,231],new_q9_record=False,new_global_bound=False,
 majority_descriptions=177062400,majority_surviving_descriptions=679,majority_distinct_sets=623,
 numerical_cuts_kernel_checked=623,full_cut_to_path_lean_assembly=False,finite_enumeration_lean_checked=False,
 full_enumeration_rerun_this_resumption=False,independent_finite_input_audit_sha256=sha(H/'data/finite-input-audit.json'),
 maximum_seed_overlap_for_192=186,minimum_old_vertices_omitted=6,minimum_new_vertices_added=7,
 actual_cube_inverse_lean_checked=True,two_missing_neighbour_counts_lean_checked=True,
 proofs=proofs,documents=docs,document_review_sha256=sha(review),
 contributor_revision='478869ee1ec6ff3a10ddb6ba7a2a1d89fbb82088',contributor_231_completed=True,independent_231_rebuild=False,
 four_excluded=prior['four_excluded'],four_unknown=prior['four_unknown'],four_unqueried=prior['four_unqueried'],
 frozen_parent_search_states=prior['frozen_parent_search_states'],full_manuscript_review_round=230,next_full_manuscript_review_round=240,
 next_step='Investigate recovery with three or more erased neighbour counts, for construction consistency; stop after round239.')
(H/'data/completion.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print('COMPLETE237',len(proofs),'proof receipts',len(checked),'dependency files')
