from pathlib import Path
import json,hashlib
H=Path(__file__).resolve().parents[1];R=H.parents[1]
def read(p):return json.loads(p.read_text(encoding='utf-8-sig'))
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
rp=H/'data/Undominated167-audit.json';q=read(rp)
assert q['status']=='PASS' and q['exit_code']==0 and q['stop_reason'] is None and len(q['axioms'])==6
assert all(set(x['axioms'])<={'propext','Classical.choice','Quot.sound'} for x in q['axioms'])
for f,k in [('source','source_sha256'),('object','olean_sha256'),('log','log_sha256')]:assert sha(q[f])==q[k]
for p,d in q['dependencies'].items():assert sha(p)==d,p
ex=read(H/'review/equality-example.json');assert ex['status']=='PASS_EXACT_DEGREE_ONLY_EQUALITY_EXAMPLE'
assert sha(H/'review/equality_example.py')==ex['script_sha256']
assert ex['vertices']==60 and ex['degree_at_zero']==0 and ex['empty_squares_at_zero']==4
assert ex['selected_degree_histogram']=={'1':8,'2':52}
assert ex['component_sizes']==[3]*4+[8]*6 and not ex['is_snake']
edit=read(H/'data/paper-edit.json');paper=R/'paper/snake9_research.tex';editor=Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex')
assert sha(paper)==sha(editor)==edit['after_sha256']
c=read(H/'data/paper-compile.json');assert any(json.loads(x['text']).get('kind')=='success' for x in c['content'] if x['type']=='text')
assert not (R/'work/fullgraph-active.lock').exists() and not (R/'milestones/161-share18-full-replay/data/replay-batch.lock').exists()
protected={'.gitignore':'20d6df071a62fabfd98360ddf985088445fde2dec19ef0281f5ab5c6d2b1941b','milestones/50-three-count-return/excess-screen/data/critical-family.json':'466e23170f15072cae3643971b5d9a62b2227fc9ffb4bca276173dc19892db82'}
for p,d in protected.items():assert sha(R/p)==d
paths=[rp,H/'review/PROOF_REVIEW.md',H/'review/equality-example.json',H/'review/equality_example.py',H/'data/paper-edit.json',H/'data/paper-compile.json',Path(__file__)]
j=dict(status='PASS_LOCAL_LOGIC_AND_WRITTEN_UNDOMINATED_CORNER_PROOF',evidence_sha256={str(p.relative_to(H)).replace('\\','/'):sha(p) for p in paths},new_Lean_logic_statements=6,written_degree_only_bound=4,written_snake_bound_at_undominated_corner=5,written_loss_contribution_lower_bound=60,complete_Q9_Lean_theorem=False,remaining_Lean_obligations=['Interpret pair and triple predicates from a translated Q9 selected set.','Prove coverage cardinality and the equality matching case.','Count eight distinct forced degree-one vertices.','Connect the local theorem to the global remainder sum.'],universal_positive_loss_bound=False,new_numerical_snake_bound=False,paper_sha256=sha(paper),paper_compiled=True,last_full_paper_revision=166,latest_paper_addition=167,next_full_paper_revision=176,protected_files_sha256=protected,initial_small_module_startup_stop_free_bytes=1033142272,replay_deductions_unchanged=33111,requested_rounds_completed=[166,167])
(H/'data/completion.json').write_text(json.dumps(j,indent=2)+'\n',encoding='utf-8')
header='''# Two-round stopping point: small loss and undominated corners

Rounds 166 and 167 are complete. Research stops here for the requested
bounded continuation. No research worker remains running.

Round 166 checked six finite degree/remainder statements in Lean, audited
all 131 saved 191-edge snakes, and produced explicit zero-loss disconnected
countermodels. The complete paper received its scheduled revision and
compiled successfully with its original preamble, hyperlink settings,
and authors preserved.

Round 167 gives a written geometric proof: if every selected vertex has
degree one or two, an undominated cube vertex lies on at least four empty
squares. Equality forces eight selected degree-one vertices. Hence for a
nontrivial snake, an undominated vertex lies on at least five empty squares
and contributes at least60 to total rounding loss. Therefore total loss
at most59 forces every cube vertex to have a selected neighbour.

Six supporting logical and arithmetic statements passed Lean. The full
Q9 interpretation, coverage/matching counting, distinct endpoint count,
and global-sum assembly remain pending. The written theorem must not be
labelled a complete Lean-checked arbitrary-snake theorem. The degree-only
bound four has an exactly checked 60-vertex equality example with eight
endpoints; it is disconnected and is not a snake.

The target loss-at-most-three case is thus restricted to dominating
snakes. This does not exclude it. The printed 191-edge witness already
has this domination property. There is no new numerical upper bound.
The earlier conditional234comparison still needs its loss and inherited
geometric/certificate premises. The large replay remains at33,111checked
deductions; no new replay deductions were attempted in these two rounds.

Read milestones/167-undominated-corners/COMPLETION.md and its adjacent
data/completion.json for the exact scope. The full proof appears in
review/PROOF_REVIEW.md and in the updated paper. Last full paper revision:
166; latest mathematical addition:167; next scheduled full revision:176.

'''
for a,b in [('least60','least 60'),('most59','most 59'),('conditional234comparison','conditional 234 comparison'),('at33,111checked','at 33,111 checked'),('addition:167','addition: 167'),('revision:176','revision: 176')]:header=header.replace(a,b)
body=header+'''On resumption, first confirm the actual process state and inspect Git
updates. The next proof task is to connect the checked pair/triple logic
to the existing cube and square definitions, preserving all selected-degree
and endpoint hypotheses. Existing sources include work/spectral/SquareIncidence.lean,
work/final_lean/CubeLocal.lean, and the milestone73 bridge's CoreShareBudget.
The native zero-loss examples show why degree and endpoint conditions
alone, or acyclicity alone, cannot establish a positive loss bound.

A further mathematical target is a restriction coupling domination with
the exact degree-five residue table and the length-at-least235 hypothesis.
Domination on its own is insufficient. Any numerical search must keep
connectedness, inducedness, and the two-endpoint condition explicit.

The core-only Lean checks use a separate resource profile:1GiB startup,
768MiB free reserve and256MiB sampled compiler-private cap. An initial
startup gate stopped before compilation; the later run passed. The large
replay's original2GiB startup gate and other resource limits were unchanged.
Historical completion files pin the bytes at their publication commits;
the new paper supersedes the earlier paper hashes without altering those
historical records. The editor file and repository mirror agree.
'''
for a,b in [('milestone73','milestone 73'),('least235','least 235'),('profile:1GiB','profile: 1 GiB'),('768MiB','768 MiB'),('and256MiB','and 256 MiB'),('original2GiB','original 2 GiB')]:body=body.replace(a,b)
(H/'COMPLETION.md').write_text(body,encoding='utf-8')
for rel in ['README.md','handoff/CURRENT_STATUS.md','handoff/NEXT_AGENT_PROMPT.md']:
 p=R/rel;p.write_bytes((header+'Historical records follow.\n\n').encode()+p.read_bytes())
print(j['status'])
