from pathlib import Path
import hashlib,json,datetime
H=Path(__file__).resolve().parents[1];R=H.parents[1];D=Path('D:/Codex/2026-10-13/new-chat/outputs')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):return json.loads(Path(p).read_bytes())
replay=read(H/'data/coefficients-replay.json');assert replay['status']=='PASS'
proofs=[];pins={}
for item in replay['modules']:
 p=H/'data'/(item['module']+'-audit.json');d=read(p);assert d['status']=='PASS'
 for key,hkey in [('source','source_sha256'),('object','olean_sha256'),('log','log_sha256')]:assert sha(d[key])==d[hkey]
 for f,h in d['dependencies'].items():
  if f not in pins:pins[f]=sha(f)
  assert pins[f]==h,f
 assert 'sorryAx' not in Path(d['log']).read_text(encoding='utf-8')
 proofs.append(dict(module=item['module'],receipt_sha256=sha(p),reports=len(d['axioms'])))
docs={}
for name in ['snake9_research','snake9_frontier_explanation']:
 a=D/(name+'.tex');b=R/'paper'/(name+'.tex');assert a.read_bytes()==b.read_bytes()
 p=H/'data'/(name+'-compile.json');assert json.loads(read(p)['content'][0]['text'])['kind']=='success'
 docs[name+'.tex']=dict(editor=str(a),mirror=str(b),sha256=sha(a),compile_sha256=sha(p))
review=H/'logs/final-document-review.json';assert read(review)['status']=='PASS_BOUNDED_DOCUMENT_REVIEW'
prior=read(R/'milestones/237-parity-reconstruction/data/completion.json')
keep=['interval','contributor_revision','contributor_231_completed','independent_231_rebuild','four_excluded','four_unknown','four_unqueried','frozen_parent_search_states','full_manuscript_review_round','next_full_manuscript_review_round','maximum_seed_overlap_for_192','minimum_old_vertices_omitted','minimum_new_vertices_added']
out={k:prior[k] for k in keep}
for v in out['frozen_parent_search_states'].values():assert sha(R/v['path'])==v['sha256']
out.update(round=238,status='PROGRESS',goal_status='ACTIVE_CONTINUE_THROUGH_239',pause_after_round=239,
 started_utc='2026-11-18 11:03:50 UTC',finished_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
 new_q9_record=False,new_global_bound=False,missing_counts_recoverable_lean=3,observed_counts_sufficient=509,
 known_parity_observed_counts_sufficient_written=253,arithmetic_coefficient_cases=125,arithmetic_rhs_cases=3375,
 arithmetic_unbounded_version='written proof; Lean retains automatic bounds9',
 proofs=proofs,documents=docs,document_review_sha256=sha(review),
 next_step='Analyze four missing counts using parity blocks and coordinate-permutation symmetry; then stop after239.')
(H/'data/completion.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8',newline='\n')
print('COMPLETE238',len(proofs),'acceptedmodules')
