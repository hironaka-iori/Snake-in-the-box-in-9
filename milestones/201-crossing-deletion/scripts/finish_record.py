from pathlib import Path
import datetime,hashlib,json,re,subprocess

H=Path(__file__).resolve().parents[1]; R=H.parents[1]
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def save(p,d): p.write_bytes((json.dumps(d,indent=2)+'\n').encode('utf-8'))
def git(*args):
    return subprocess.check_output(['git','-c','core.commitGraph=false','-c','maintenance.auto=false','-c','gc.auto=0',*args],cwd=R)

modules=['CrossingDeletion201','LayerEndpoint201','TwoParents201','EndpointGeometry201','OverlapEquality201','CutObstruction201']
proofs=[]
for module in modules:
    receipt=H/'data'/(module+'-audit.json'); d=json.loads(receipt.read_bytes())
    assert d['status']=='PASS' and d['exit_code']==0 and d['stop_reason'] is None
    for p,h in d['dependencies'].items(): assert sha(p)==h,p
    for path,hashkey in [('source','source_sha256'),('object','olean_sha256'),('log','log_sha256')]: assert sha(d[path])==d[hashkey]
    assert all(set(x['axioms'])<={'propext','Classical.choice','Quot.sound'} for x in d['axioms'])
    proofs.append(dict(module=module,receipt=str(receipt.relative_to(H)),sha256=sha(receipt),reports=len(d['axioms']),seconds=d['seconds']))

seedpath=R/'milestones/188-dimensional-constructions/data/lower-dimensional-seeds.json'; seeds=json.loads(seedpath.read_bytes())
cutsource=H/'lean/CutObstruction201.lean'; code=cutsource.read_text(encoding='utf-8')
saved=[int(x) for x in re.findall(r'\d+',code.split('def vertices : List Nat :=',1)[1].split('def crossings',1)[0])]
assert saved==seeds['8']['vertices']
comparison=dict(source=str(seedpath),source_sha256=sha(seedpath),lean_source_sha256=sha(cutsource),same_vertex_list=True,
                profiles={n:[{k:p[k] for k in ['coordinate','crossings','face_vertices','component_edges']} for p in seeds[n]['profiles']] for n in ['7','8']},
                scope='Existing round188 profiles read; the Q8 all-coordinate obstruction is newly kernel-checked in CutObstruction201. No new construction search.')
save(H/'data/dimensional-comparison.json',comparison)

base='0cb8450707e481db49b6204587e45db9ae0df589'
head=git('rev-parse','origin/research/unconditional-241').decode().strip()
assert head=='816bbcf557c946227151bc4cee48357f1e7a4d65','Contributor changed; inspect new work before recording.'
diff=git('diff',base+'..'+head,'--','milestones/33-233-lean/CERT-PROGRESS.md','milestones/33-233-lean/certify/data/replay6SB233.jsonl')
(H/'logs/contributor-final.diff').write_bytes(diff)
progress=git('show',head+':milestones/33-233-lean/CERT-PROGRESS.md')
(H/'logs/contributor-progress.md').write_bytes(progress)
contributor=dict(base=base,head=head,changed=head!=base,diff_sha256=sha(H/'logs/contributor-final.diff'),reported_built=3005,reported_total=3127,
                 scope='Contributor 05:49 UTC progress report inspected; no local independent rebuild or merge. Archived235 rebuild remains pending;233/234 remain conditional.')
save(H/'data/contributor-final.json',contributor)

editor=Path('D:/Codex/2026-10-13/new-chat/outputs')
for name in ['snake9_research.tex','snake9_frontier_explanation.tex']:
    assert (editor/name).read_bytes()==(R/'paper'/name).read_bytes()
for name in ['main','frontier']:
    d=json.loads((H/'data'/(name+'-compile.json')).read_bytes())
    assert d['isError'] is False
    assert any(json.loads(c['text']).get('kind')=='success' for c in d['content'] if c['type']=='text')

completion=dict(round=201,status='PROGRESS',previous_turn_classification='PROGRESS: round200 completed a native trimming census, six Lean deductions and the whole-manuscript review.',
                goal_status='pause_requested_after_publication',utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),base_head=git('rev-parse','HEAD').decode().strip(),
                new_q9_record=False,new_global_bound=False,solver_searches=[],accepted_lean_modules=modules,theorem_reports=sum(p['reports'] for p in proofs),proofs=proofs,
                checked_scope='Generic Boolean-list accounting, explicit count-equation composition, numerical implications, actual induced-path endpoint geometry, overlap equality, two small concrete paths and the Q8 all-coordinate obstruction.',
                written_proof_scope='Full arbitrary-graph count interpretation, exact one-deletion classification, and composed C=5 attachment restriction.',
                key_consequences=['L+k<=2a(n)+2+2A for the specified two-parent construction','The saved98-edge Q8 witness has no deletion-only two-Q7-parent representation in any coordinate split','A deletion-only196-edge Q9 construction has at most one deletion and at most two crossings','With196 edges,k>=4,A=1, the addition must be a global endpoint; its195-edge predecessor has3 crossings andC<=5'],
                commentary_correction='At least two additions for196 edges and4 crossings requires both final endpoints to be original vertices. With one added endpoint the equality alternative is unresolved.',
                contributor=contributor,compiled_documents=['main','frontier'],whole_manuscript_review_round=200,next_whole_manuscript_review_round=210,
                next_action='Pause after confirmed publication. Resume only on new user instruction, prioritizing exact parent compatibility proofs for the one-deletion196 criterion or195-edge three-crossing predecessor. Round200 catalogue is secondary.')
save(H/'data/completion.json',completion)
print('SAVED_ROUND201',len(modules),'modules',completion['theorem_reports'],'reports; both documents compiled; no new solver search.')
