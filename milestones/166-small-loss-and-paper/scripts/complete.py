from pathlib import Path
import json,hashlib
H=Path(__file__).resolve().parents[1];R=H.parents[1]
def read(p):return json.loads(p.read_text(encoding='utf-8-sig'))
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
q=read(H/'data/CornerLoss166Core-audit.json')
assert q['status']=='PASS' and q['exit_code']==0 and q['stop_reason'] is None and len(q['axioms'])==6
assert all(not a['axioms'] for a in q['axioms'])
for f,k in [('source','source_sha256'),('object','olean_sha256'),('log','log_sha256')]:assert sha(q[f])==q[k]
for p,d in q['dependencies'].items():assert sha(p)==d,p
x=read(H/'experiment/results.json');assert x['status']=='PASS_EXACT_FINITE_LOSS_AUDIT'
assert sha(H/'experiment/audit_loss.py')==x['script_sha256']
for p,d in x['input_sha256'].items():assert sha(R/p)==d,p
assert (x['control191']['loss'],x['bank191']['count'],x['bank191']['minimum'],x['bank191']['maximum'])==(163,131,152,913)
for key in ['degree_two_zero_loss','two_endpoints_zero_loss','acyclic_zero_loss','rank_four_zero_loss']:assert x[key]['loss']==0 and not x[key]['is_induced_path']
assert x['rank_four_zero_loss']['component_sizes']==[6]*16
paper=R/'paper/snake9_research.tex';editor=Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex')
edit=read(H/'data/paper-edit.json');assert sha(paper)==sha(editor)==edit['after_sha256']
c=read(H/'data/paper-compile.json');assert any(json.loads(a['text']).get('kind')=='success' for a in c['retry']['content'] if a['type']=='text')
protected={'.gitignore':'20d6df071a62fabfd98360ddf985088445fde2dec19ef0281f5ab5c6d2b1941b','milestones/50-three-count-return/excess-screen/data/critical-family.json':'466e23170f15072cae3643971b5d9a62b2227fc9ffb4bca276173dc19892db82'}
for p,d in protected.items():assert sha(R/p)==d
pins={str(p.relative_to(H)).replace('\\','/'):sha(p) for p in [H/'data/CornerLoss166Core-audit.json',H/'experiment/results.json',H/'experiment/audit_loss.py',H/'experiment/FINDINGS.md',H/'review/full-paper-review.md',H/'data/paper-edit.json',H/'data/paper-compile.json',Path(__file__)]}
j=dict(status='PASS_FINITE_LOSS_ARITHMETIC_COUNTERMODELS_AND_PAPER166',evidence_sha256=pins,new_Lean_statements=6,arithmetic_axioms=[],geometric_cap_assumed_in_Lean=True,universal_loss_lower_bound_proved=False,new_unconditional_bound=False,paper_sha256=sha(paper),paper_compiled=True,paper_full_revision=166,next_full_revision=176,protected_files_sha256=protected,unexecuted_mathlib_source='lean/CornerLoss166.lean',core_resource_profile='1 GiB startup, 768 MiB reserve, 256 MiB sampled compiler-private cap; existing large replay unchanged',initial_core_startup_stop_free_bytes=994840576)
(H/'data/completion.json').write_text(json.dumps(j,indent=2)+'\n',encoding='utf-8')
header='''# Round 166: exact small-loss restrictions and zero-loss countermodels

Six finite arithmetic statements passed Lean with no axioms. They cover
all possible Q9 degrees and incident-square counts, conditional on the
geometric bound e(q) <= choose(9-d(q),2). The geometric bound is proved
in the paper by assigning each empty square its two absent-neighbour
directions; that geometric interpretation is not newly checked in Lean.

Loss at most three excludes positive empty-square counts at degrees zero
and seven, excludes count two at degree five, and permits at most three
positive degree-five residues. Count five at degree five has zero residue.

The independent exact audit checks the explicit 191-edge snake (loss163)
and all 131 bank snakes (loss152 through913). It also gives zero-loss
countermodels: a disconnected degree-two set; a disconnected set with
exactly two endpoints and cycles; an acyclic set with64endpoints; and a
union of sixteen six-cycles. None is a snake or a counterexample at235edges.
Thus no universal positive-loss bound has been established.

The existing paper and its repository mirror were updated in place,
reviewed against all6,605 prior lines, and compiled by the editor. The
preamble, local hyperlink settings, and three authors were preserved.
The update integrates the exact loss budget, degree decomposition,
conditional234comparison, finite tests, and current replay status.
The first compilation returned stale-project; the retry succeeded.
The six Lean checks used the core library with a separate small-memory
profile. The initial core startup gate stopped before compilation; the
later run passed. The large replay's original resource limits remain
unchanged. Its accepted prefix is still33,111deductions.

Read experiment/FINDINGS.md for constructions, data/completion.json for
scope and hashes, and review/full-paper-review.md for the source review.
Last full paper revision:166. Next scheduled full revision:176.
'''
for a,b in [('loss163','loss 163'),('loss152','loss 152'),('through913','through 913'),('with64endpoints','with 64 endpoints'),('at235edges','at 235 edges'),('all6,605','all 6,605'),('conditional234comparison','conditional 234 comparison'),('still33,111deductions','still 33,111 deductions'),('revision:166','revision: 166'),('revision:176','revision: 176')]:header=header.replace(a,b)
(H/'COMPLETION.md').write_text(header,encoding='utf-8')
for rel in ['README.md','handoff/CURRENT_STATUS.md','handoff/NEXT_AGENT_PROMPT.md']:
 p=R/rel;p.write_bytes((header+'\nHistorical records follow.\n\n').encode()+p.read_bytes())
print(j['status'])
