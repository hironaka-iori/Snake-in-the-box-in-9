from pathlib import Path
import hashlib,json,datetime
H=Path(__file__).resolve().parents[1]; R=H.parents[1]
D=Path('D:/Codex/2026-10-13/new-chat/outputs')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):return json.loads(Path(p).read_bytes())
replay=read(H/'data/matrices-replay.json');assert replay['status']=='PASS' and len(replay['modules'])==372
modules=[x['module'] for x in replay['modules']]+['EightCubeObstruction240']
proofs=[];pins={}
for name in modules:
 p=H/'data'/(name+'-audit.json');d=read(p)
 assert d['status']=='PASS' and d['exit_code']==0 and d['stop_reason'] is None
 for k,h in [('source','source_sha256'),('object','olean_sha256'),('log','log_sha256')]:assert sha(d[k])==d[h]
 for f,h in d['dependencies'].items():
  if f not in pins:pins[f]=sha(f)
  assert pins[f]==h,f
 assert 'sorryAx' not in Path(d['log']).read_text(encoding='utf-8')
 proofs.append(dict(module=name,receipt_sha256=sha(p),reports=len(d['axioms'])))
assert sum(x['reports'] for x in proofs)==380
audit=read(H/'data/five-count-audit.json');assert audit['status']=='PASS_NO_NONZERO_INTEGER_SOLUTIONS'
assert sha(H/'scripts/audit_five.py')==audit['source_sha256']
geometry=read(H/'data/independent-geometry.json')
assert geometry['status']=='PASS_GEOMETRIC_CLASS_COVERAGE' and geometry['vertex_triples']==2699004
assert geometry['script_sha256']==sha(H/'scripts/independent_geometry.py')
docs={}
for name in ['snake9_research','snake9_frontier_explanation']:
 a=D/(name+'.tex');b=R/'paper'/(name+'.tex');assert a.read_bytes()==b.read_bytes()
 p=H/'data'/(name+'-compile.json');assert json.loads(read(p)['content'][0]['text'])['kind']=='success'
 assert read(p)['saved_source_sha256']==sha(a)
 docs[name+'.tex']=dict(editor=str(a),mirror=str(b),sha256=sha(a),compile_sha256=sha(p))
review=read(H/'logs/final-document-review.json');assert review['status']=='PASS_BOUNDED_DOCUMENT_REVIEW'
old_main=sha(H/'data/snake9_research-before.tex');old_short=sha(H/'data/snake9_frontier_explanation-before.tex')
p1=read(H/'logs/full-review-part1.json');p2=read(H/'logs/full-review-part2.json');p3=read(H/'logs/full-review-part3.json')
assert p1['source_sha256']==old_main and p1['assigned_lines']==[1,4400]
assert p2['source']['sha256']==old_main and p2['coverage']['first_line']==4401 and p2['coverage']['last_line']==8800 and p2['coverage']['complete']
assert p3['main_source']['sha256']==old_main and p3['main_source']['coverage']==[8801,13254]
assert p3['short_source']['sha256']==old_short and p3['short_source']['coverage']==[1,1084]
full=dict(status='COMPLETE_WRITTEN_SOURCE_REVIEW',round=240,next_due_round=250,pre_edit_main_sha256=old_main,pre_edit_main_lines=13254,main_coverage=[[1,4400],[4401,8800],[8801,13254]],pre_edit_short_sha256=old_short,pre_edit_short_lines=1084,short_coverage=[1,1084],parts={str(p.relative_to(H)):sha(p) for p in [H/'logs/full-review-part1.json',H/'logs/full-review-part2.json',H/'logs/full-review-part3.json']},integrated_delta_review_sha256=sha(H/'logs/final-document-review.json'),documents=docs,scope='Complete written-source reading plus integrated delta review and saved-source compilation. Does not independently rebuild all archived Lean dependencies or numerical certificates; no visual PDF inspection claimed.')
(H/'logs/full-manuscript-review.json').write_text(json.dumps(full,indent=2)+'\n',encoding='utf-8',newline='\n')
prior=read(R/'milestones/239-four-count-recovery/data/completion.json')
keep=['interval','contributor_revision','contributor_231_completed','independent_231_rebuild','four_excluded','four_unknown','four_unqueried','frozen_parent_search_states','maximum_seed_overlap_for_192','minimum_old_vertices_omitted','minimum_new_vertices_added']
out={k:prior[k] for k in keep}
for value in out['frozen_parent_search_states'].values():assert sha(R/value['path'])==value['sha256']
out.update(round=240,status='PROGRESS',completed_requested_rounds=[240],goal_status='PAUSE_REQUESTED_AFTER_PUBLICATION',pause_after_round=240,started_utc=read(H/'data/round-start.json')['started_utc'],finished_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),new_q9_record=False,new_global_bound=False,missing_counts_recoverable_full_cube_lean=3,missing_counts_recoverable_written_unconditional=5,unconditional_observations=507,known_parity_observations_written=251,conditional_missing_counts=8,conditional_hypothesis='No two missing positions have Hamming distance8',conditional_bound_sharp_for_binary_selections=True,minimum_nonzero_profile_support_written=[6,9],unrestricted_nine_support_conjecture='OPEN',metric_classes=372,valid_column_descriptions=5160,column_compositions=6435,direct_vertex_triples=2699004,rhs_cases=90396,five_cube_lean_assembly=False,four_cube_lean_assembly=False,conditional_eight_cube_lean_assembly=False,eight_point_unbounded_integer_claim=False,eight_point_explicit_witness_lean=True,eight_point_bounded_classification='WRITTEN',star_family_exclusion='WRITTEN',same_parity_reduction_through_eight='WRITTEN',arithmetic_scope='372 literal integer matrix implications plus explicit eight-point obstruction with8 axiom reports. Written cube applications and structural classifications remain separate.',proofs=proofs,documents=docs,document_review_sha256=sha(H/'logs/final-document-review.json'),full_manuscript_review_round=240,next_full_manuscript_review_round=250,full_manuscript_review_sha256=sha(H/'logs/full-manuscript-review.json'),native_audit_sha256=sha(H/'data/five-count-audit.json'),independent_geometry_sha256=sha(H/'data/independent-geometry.json'),structural_note_sha256=sha(H/'STRUCTURAL_NOTE.md'),contributor_branch_last_seen=read(H/'data/contributor-status.json')['branch_revision'],contributor_status_sha256=sha(H/'data/contributor-status.json'),next_step='After explicit resumption only: classify bounded connected generator-coordinate configurations for6–8 missing counts, retaining cross-component coupling; alternatively finish4/5 actual-cube Lean assembly. No round241 work started.')
(H/'data/completion.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8',newline='\n')
print('COMPLETE240',len(proofs),'accepted modules;',sum(x['reports'] for x in proofs),'axiom reports; frozen states match.')
