from pathlib import Path
import datetime,hashlib,json,subprocess
H=Path(__file__).resolve().parents[1];R=H.parents[1]
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(name):return json.loads((H/'data'/(name+'.json')).read_bytes())
git=['git','-c','core.commitGraph=false','-c','maintenance.auto=false','-c','gc.auto=0']
def output(*args):return subprocess.check_output(git+list(args),cwd=R)
base='0cb8450707e481db49b6204587e45db9ae0df589';head=output('rev-parse','origin/research/unconditional-241').decode().strip();diff=output('diff',base+'..'+head)
(H/'logs/contributor-final.diff').write_bytes(diff)
contributor=dict(base=base,head=head,changed=head!=base,diff_sha256=hashlib.sha256(diff).hexdigest(),scope='No branch change since round199 at final fetch; no merge or independent rebuild.')
assert head==base
(H/'data/contributor-refresh.json').write_text(json.dumps(contributor,indent=2)+'\n',encoding='utf-8',newline='\n')
trim=read('trim-census');cat=read('catalogue-d4');maps=read('low-overlap-maps');proof=read('CollisionRepair200-audit')
assert trim['status']=='COMPLETE' and trim['maximum_forest_vertices']==92 and trim['first_intervals_examined']==89958
assert sum(trim['intersection_histogram'].values())==645120 and trim['eligible_isometries']==1363
assert len(maps['rows'])==16 and len(maps['representatives'])==15
assert cat['status']=='DEFERRED' and len(cat['rows'])==2 and all(r['status']=='INFEASIBLE' for r in cat['rows'])
assert proof['status']=='PASS' and len(proof['axioms'])==6
for p,d in proof['dependencies'].items():assert sha(p)==d,p
assert sha(proof['source'])==proof['source_sha256'] and sha(proof['object'])==proof['olean_sha256']
searches=[]
for name in ['coupled100-case0-d4','coupled100-case1-d4','coupled100-case0-d6','coupled100-case1-d6']:
 d=read(name);searches.append(dict(record=name,status=d['status'],seconds=d['seconds'],arguments=d['arguments'],sha256=sha(H/'data'/(name+'.json'))))
review=read('manuscript-review');reports=[dict(path=p,sha256=sha(H/p)) for p in review['review_reports']]
out=dict(round=200,status='PROGRESS',previous_turn_classification='PROGRESS: round199 completed full-isometry censuses for saved parent banks and checked general placement deductions.',goal_status='pause_requested_after_publication',utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),base_head=output('rev-parse','HEAD').decode().strip(),new_q9_record=False,new_global_bound=False,accepted_lean_modules=['CollisionRepair200'],theorem_reports=6,numerical_censuses_lean_checked=False,trim_maximum_forest_vertices=92,trim_isometries=645120,trim_eligible_maps=1363,trim_first_intervals=89958,low_overlap_maps=16,inverse_pair_representatives=15,excluded_d4_representatives=[r['case'] for r in cat['rows']],pending_d4_representatives=[i for i in maps['representatives'] if not any(r['case']==i for r in cat['rows'])],catalogue_status=cat['status'],solver_searches=searches,full_manuscript_review=reports,contributor=contributor,next_action='Pause after publication at user request. Resume only on new user instruction; first finish the13 pending four-omission inverse-pair cases when startup memory is available. Do not rerun unchanged six-omission timeouts.')
(H/'data/completion.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8',newline='\n')
handoff='''# Current state after round 200

The user requested a pause after this round. Publication is the final work for this round; set the goal to paused after confirming the push, and do not start further research until the user resumes it. No new Q9 witness or global bound was obtained.

Read milestones/200-overlap-repair/MATHEMATICAL_NOTE.md and data/completion.json. The complete native trimming census gives an exact maximum of 92 separated Q8 vertices from two independently trimmed copies of the one published 51-vertex Q7 parent, over all 645120 relative cube isometries. Every competitive pair deletes at most10 original vertices. Since each collision needs a deletion, only1363 maps remain;66 first-parent intervals per map and the largest collision-free second gap give89958 cases. The saved92 witness uses positions5 through50 in both parents for swaps(1,4),(3,6), XOR126. The earlier96-vertex paired forest changes the parent shape and is outside this family.

Six Lean reports in CollisionRepair200 pass: the Boolean overlap-cover step, its finite sum, the100-vertex repair identity D=A+2, the trimming cutoff, and two interval implications giving89 and92 at the minimum-overlap maps. Concrete collision positions and the full numerical census remain native; no all-isometry Lean replay is claimed.

The two variable-path repair models allow49 to51 vertices per Q7 path, total100, disjoint projected sets, free endpoints and no required symmetry of the final paths. At the two minimum-overlap placements, total omission budget4 is INFEASIBLE in3.125 and2.594 seconds. For those two placements, any100-vertex repair needs at least5 omissions and3 additions. Budget6 is UNKNOWN60.032 and60.000 seconds. These are native solver results without Lean contradiction certificates.

There are exactly16 starting isometries with at most4 original overlaps:14 involutions and one inverse pair of noninvolutions, giving15 representative repair cases. The saved low-overlap-maps.json gives every map, collision position and inverse index. Catalogue cases4 and13 reuse the two established exclusions. The other13 representatives are unrun because available memory did not meet the startup requirement. The bounded resume attempt is terminal with status DEFERRED; no worker remains scheduled. Memory refusals and waiting snapshots are saved.

On a new user resume, run scripts/resume_catalogue.py after sufficient memory is available. It preserves earlier attempts and reuses existing results. For noninvolutions no within-instance omission-order constraint is imposed; inverse-case reduction swaps parents and applies the inverse isometry. Complete exclusion requires all15 representatives to be INFEASIBLE. A found100-vertex face still needs93 opposite-face vertices for192 edges,95 for194, or97 for196. If every four-omission case fails, larger budgets require a correspondingly enlarged overlap catalogue. Do not repeat the unchanged six-omission timeouts.

The whole main source (8964 pre-edit lines) and explanation (961 pre-edit lines) were read across three bounded reviews. The paper corrects an unsuccessful historical merger described as a construction, identifies the changed quotient, qualifies finite-walk averages by boundary terms, distinguishes old and current floors, defines loss/window notation at first use, reconciles contact and intersection counts, clarifies representative transport, preserves archived235 qualifications, and updates the abstract/frontier. This source review does not rebuild archived proofs or replay every certificate.

Contributor branch remains0cb8450707e481db49b6204587e45db9ae0df589 at final fetch. No merge or independent rebuild. Archived235 rebuild remains pending;233/234 remain conditional. Next whole-manuscript review at210 if research resumes.

Editor sources remain D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex and snake9_frontier_explanation.tex, mirrored in E:/Snake-in-a-box/paper. Preserve authors, hypersetup, and unrelated .gitignore and milestone50 edits. Keep one heavy worker,1GiB startup free memory,768MiB reserve,256MiB per Lean process and60-second Lean checks. The catalogue runner waits for1280MiB before importing the solver to leave room for startup overhead. Resume only at user request.
'''
for name in ['CURRENT_STATUS.md','NEXT_AGENT_PROMPT.md']:(R/'handoff'/name).write_text(handoff,encoding='utf-8',newline='\n')
brief='''# Round 200: overlap counting and complete trimming restriction

Two independently trimmed copies of the published50-edge Q7 parent give at most92 separated Q8 vertices, over all645120 cube isometries. The native census uses a checked overlap/deletion argument to reduce the search to1363 maps and89958 first intervals. The numerical census itself has no Lean replay.

Six general counting and interval statements pass Lean. Four-omission coupled repairs fail at the two minimum-overlap placements; six-omission queries remain UNKNOWN. A complete low-overlap catalogue has15 inverse-pair representatives, of which13 remain unrun because startup memory was unavailable.

The whole manuscript and explanation were reviewed and corrected, with authors and hyperlink settings preserved. Read [the argument](MATHEMATICAL_NOTE.md), [completion record](data/completion.json), [trimming census](data/trim-census.json), [repair catalogue](data/low-overlap-maps.json), and [handoff](../../handoff/CURRENT_STATUS.md). Models are packaged in data/solver-models.zip. No new Q9 witness or global numerical bound is claimed. The user requested a pause after this round; resume only on new instruction.
'''
(H/'README.md').write_text(brief,encoding='utf-8',newline='\n')
p=R/'README.md';s=p.read_text(encoding='utf-8');assert not s.startswith('# Current result after round 200')
prefix='''# Current result after round 200

A complete native census limits two independently trimmed copies of the specified Q7 parent to92 separated Q8 vertices, even with every cube isometry allowed. Six counting and interval deductions pass Lean. Coupled four-omission repairs are excluded at two starting placements;13 further representative cases are saved for continuation. No new Q9 witness or global bound is claimed.

The entire manuscript and frontier explanation were reviewed and corrected. The user requested a pause after this round. Read [round200](milestones/200-overlap-repair/README.md), [the argument](milestones/200-overlap-repair/MATHEMATICAL_NOTE.md), [verification status](milestones/200-overlap-repair/data/completion.json), [handoff](handoff/CURRENT_STATUS.md), and [frontier explanation](paper/snake9_frontier_explanation.tex). Resume research only on new user instruction.

## Earlier checkpoints

'''
p.write_text(prefix+s,encoding='utf-8',newline='\n');print('SAVED_ROUND200_PAUSE_HANDOFF')
