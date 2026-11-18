from pathlib import Path
import hashlib,json,datetime
H=Path(__file__).resolve().parents[1];R=H.parents[1];D=Path('D:/Codex/2026-10-13/new-chat/outputs')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):return json.loads(Path(p).read_bytes())
proofs=[];pins={}
for tag in ['matrices','dominance']:
 replay=read(H/'data'/(tag+'-replay.json'));assert replay['status']=='PASS'
 for item in replay['modules']:
  p=H/'data'/(item['module']+'-audit.json');d=read(p);assert d['status']=='PASS' and d['exit_code']==0 and d['stop_reason'] is None
  for key,hkey in [('source','source_sha256'),('object','olean_sha256'),('log','log_sha256')]:assert sha(d[key])==d[hkey]
  for f,h in d['dependencies'].items():
   if f not in pins:pins[f]=sha(f)
   assert pins[f]==h,f
  assert 'sorryAx' not in Path(d['log']).read_text(encoding='utf-8')
  proofs.append(dict(module=item['module'],receipt_sha256=sha(p),reports=len(d['axioms'])))
assert len(proofs)==90
audit=read(H/'data/four-count-audit.json');assert audit['status']=='PASS_NO_NONZERO_INTEGER_SOLUTIONS'
assert sha(H/'scripts/audit_four.py')==audit['source_sha256']
assert read(H/'data/independent-geometry.json')['status']=='PASS_GEOMETRY_COVERAGE'
docs={}
for name in ['snake9_research','snake9_frontier_explanation']:
 a=D/(name+'.tex');b=R/'paper'/(name+'.tex');assert a.read_bytes()==b.read_bytes()
 p=H/'data'/(name+'-compile.json');assert json.loads(read(p)['content'][0]['text'])['kind']=='success'
 docs[name+'.tex']=dict(editor=str(a),mirror=str(b),sha256=sha(a),compile_sha256=sha(p))
review=H/'logs/final-document-review.json';assert read(review)['status']=='PASS_BOUNDED_DOCUMENT_REVIEW'
prior=read(R/'milestones/238-three-count-recovery/data/completion.json')
keep=['interval','contributor_revision','contributor_231_completed','independent_231_rebuild','four_excluded','four_unknown','four_unqueried','frozen_parent_search_states','full_manuscript_review_round','next_full_manuscript_review_round','maximum_seed_overlap_for_192','minimum_old_vertices_omitted','minimum_new_vertices_added']
out={k:prior[k] for k in keep}
for v in out['frozen_parent_search_states'].values():assert sha(R/v['path'])==v['sha256']
out.update(round=239,status='PROGRESS',completed_requested_rounds=[237,238,239],goal_status='PAUSE_REQUESTED_AFTER_PUBLICATION',pause_after_round=239,
 started_utc=audit['started_utc'],finished_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
 new_q9_record=False,new_global_bound=False,missing_counts_recoverable_full_cube_lean=3,
 missing_counts_recoverable_written_unconditional=4,unconditional_observations=508,
 known_parity_observations_written=252,conditional_missing_counts=8,
 conditional_hypothesis='No two missing positions have Hamming distance8',conditional_bound_sharp_for_binary_selections=True,
 minimum_nonzero_profile_support_written=[5,9],unrestricted_nine_support_conjecture='OPEN',
 metric_classes=87,point_set_orbits=105,valid_column_descriptions=1149,column_compositions=11440,
 direct_vertex_triples=2731135,rhs_cases=7047,four_cube_lean_assembly=False,conditional_eight_cube_lean_assembly=False,
 arithmetic_scope='87 literal integer matrix implications plus5 generic list/scalar statements in3 modules; written geometric applications remain separate',
 proofs=proofs,documents=docs,document_review_sha256=sha(review),
 native_audit_sha256=sha(H/'data/four-count-audit.json'),independent_geometry_sha256=sha(H/'data/independent-geometry.json'),
 contributor_branch_last_seen=read(H/'data/contributor-status.json')['branch_revision'],
 contributor_status_sha256=sha(H/'data/contributor-status.json'),
 next_step='After explicit resumption, examine the derived 6435-description cover for five missing positions; no round 240 search started.')
(H/'data/completion.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8',newline='\n')
print('COMPLETE239',len(proofs),'accepted modules;',sum(p['reports'] for p in proofs),'axiom reports')
