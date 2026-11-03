"""Write the completed local result and precise remaining comparison task."""
from pathlib import Path
import json
H=Path(__file__).resolve().parents[1];R=H.parents[1]
proof=json.loads((H/'data/proof-completion.json').read_text());assert proof['status']=='PASS_ACTUAL_012032_WEAK_EXCLUSION'
note=r"""# Milestone 140: a five-count exclusion

For every fitting canonical 012032 window in an actual snake in Q9,

\[
(\alpha_{r+1},\alpha_{r+3},\alpha_{r+5})=(3,4,3)
\quad\Longrightarrow\quad
\alpha_{r+2}\ge6\ \text{or}\ \alpha_{r+4}\ge6.
\]

This applies to either length parity and imposes no endpoint-location
condition. The counts are singleton-square counts at the five internal
vertices. No new mathematical definition is introduced.

## Evidence and proof

The bounded actual-path probe for exact counts (3,5,4,5,3) returned UNSAT
without extra cycle cuts. A separate fixed native proof run produced a
trimmed certificate with 18,606 deductions, 1,397,536 hints and 4,163 core
clauses. A complete independent Python RUP replay checked every deduction.
An independent reconstruction reproduced all 100,253 original clauses,
4,253 variable meanings and eleven count/endpoint tables.

The core never uses the lower bounds of five on the second and fourth
counts. Their 672 register variables occur in neither the core nor the
retained proof. Replacing those two unused counter entries by valid empty
endpoint counters makes the same clauses follow from the weaker intervals
[(3,3),(0,5),(4,4),(0,5),(3,3)]. The new semantic interpretation passed Lean.

The complete contradiction and actual-snake interpretation passed Lean.
The proof-completion record checks 120 CNF, semantic and contradiction
modules, the exact actual theorem, and the two weak-interpretation modules:
123 modules in this proof closure. The final semantic and actual sources
have eleven axiom reports using only propext, Classical.choice and Quot.sound.
The separate arithmetic module adds two such reports. No solver verdict
is used as an axiom. Exact sources, proof bytes, logs and hashes are retained.

Normalizing the window gives vertices 0,1,3,7,6,14,10. Each internal vertex
has twenty-one opposite corners in its seven unused directions. Its count
is the number of absent corners. The clauses express this count, the fixed
window, degree at most two, positive degree, at most two endpoints, and
ordinary square/six-cycle exclusions. These conditions are necessary for
an actual induced path. The checked contradiction excludes both intervening
counts being at most five; integer order then gives the stated disjunction.

## Consequence for the saved critical cycles

The exact count vector (3,5,4,5,3) occurs in two representations of the new
completed-profile five-cycle, edges 308566 and 3806548. The weaker theorem
also excludes (3,5,4,4,3), appearing on the earlier four-cycle at edges
2220858 and 146782. These are cycle deletions, not a new graph minimum.
The additional-share six-cycle contains no matching window and survives.
Its weight remains 496 per edge under the existing profile and credit.

The prepared evaluator reproduces the139 removal set and both weight
hashes, checks both six-direction placements and both orientations, and
requires every matching count symbol to be below six. Recognition overlap
causes one deletion and no added credit. Small preparation checks cover
7,776 count vectors and1,010 direction/placement combinations. The complete
graph evaluation has not been run in this milestone.

## Selected next optimisation

The earlier four-cycle forced a positive occurrence credit. Its removal
makes zero credit the next useful test. For mean496 and zero occurrence
credit, the comparison is below235 precisely when the potential range
R is below632:

\[
\frac{1098960+8\cdot496+R}{4200+496}<235
\quad\Longleftrightarrow\quad R<632.
\]

Lean checked the sufficient direction and the exact illustrative value
551765/2348<235 at R=602. The old range602 belongs to credit83/3; it is not
a zero-credit certificate. A new all-edge check is essential.

Next derive a fresh zero-credit evaluator from the saved140 preparation,
reproduce the139 inputs and apply only the checked weak deletion. Evaluate
both profiles. For the additional profile, the surviving six-cycle gives
mean at most496; seek a matching potential of range below632. The completed
profile's new minimum remains unknown. Keep the prepared credit83/3 version
as the pinned comparison; do not edit its audited bytes.

All inherited count-sum assumptions, the hypothetical0123104 six-count
floor25, the odd-length restriction behind pair floor9, and the additional
share assumptions remain. Complete graph-to-snake assembly and even-length
arguments are separate. No new conditional or unconditional actual-snake
upper bound is established here. The maintained interval is191–235, with
incomplete independent rebuilding of the contributor upper proof.
The optimum and196 remain unresolved. The research goal remains ACTIVE.

## Resume and document details

Read data/proof-completion.json, the independent semantic audit, and
scripts/complete_proof.py before using the new result. The original replay
driver has a known final-wrapper Mathlib path limitation; its completed
120 modules are retained, and the separate checker supplies the actual
library path for the final source. The unsuccessful directory-junction
attempt changed no proof or library bytes. Do not rerun the native solver
or completed replay merely to remove this recorded infrastructure failure.

Build objects are retained locally with audited hashes. The Git checkpoint
contains sources, proof inputs and certificates, receipts, exact compiler
snapshots and logs; regenerated build objects are excluded from publication.
The paper retains all three authors, its complete preamble and hyperlink
settings. Targeted revision140 adds no definitions. Last full revision136;
next full revision146. Compilation and PDF status are recorded separately.
The separate115 batch remains governed by its own live-process observation;
never start a duplicate driver.
"""
(H/'MATHEMATICAL_NOTE.md').write_text(note,encoding='utf-8')
summary="""# Research update: milestone 140

Lean checked a new local restriction: a canonical012032 window whose first,
third and fifth internal counts are3,4,3 must have its second or fourth count
at least6. This applies to arbitrary snakes in Q9, either parity, with no
endpoint-location assumption. The actual-window proof closure has123 modules.
The separate zero-credit arithmetic has also passed Lean.

The restriction deletes the saved completed four- and five-cycles. It leaves
the additional-share six-cycle intact. No new graph minimum or global bound
has yet been established. Next test zero occurrence credit on the strengthened
graph, evaluating both profiles. At mean496, a potential range below632
would make the comparison below235; the old range602 is for different weights.
Read milestones/140-five-cycle-window/MATHEMATICAL_NOTE.md and the proof record.

The maintained interval remains191–235 with the documented upper-proof
rebuild limitation. The paper has a targeted update140 and no new definitions.
The separate115 job has a process-backed observation in this milestone.
Goal ACTIVE; previous turn and this round both made concrete progress.
"""
(H/'README.md').write_text(summary,encoding='utf-8')
for name in ['README.md','COLLABORATION.md','RESEARCH_LEDGER.md','WORKSPACE.md','milestones/README.md','handoff/README.md','handoff/CURRENT_STATUS.md']:
 p=R/name;old=p.read_text(encoding='utf-8');assert not old.startswith('# Research update: milestone 140')
 p.write_text(summary+'\n## Earlier record\n\n'+old,encoding='utf-8')
next_prompt="""# Continue after milestone 140

Work in E:/Snake-in-a-box with the requested research skill. Preserve the
three authors, paper preamble/hypersetup and unrelated .gitignore/milestone50
changes. Use only necessary notation. Keep the existing editor source and
paper/snake9_research.tex identical. Fetch, preserve exact evidence, stage
only a verified manifest, commit, push and verify each round. Goal ACTIVE.

The canonical012032 theorem is complete: counts1,3,5 equal3,4,3 force
count2>=6 OR count4>=6. Read140/MATHEMATICAL_NOTE.md, proof-completion.json,
Weak140Actual and its receipt.123 modules comprise the checked proof closure;
ZeroCredit140 is a separate checked arithmetic result. Do not rerun the
fixed native proof or completed contradiction. Original replay's final
Mathlib lookup limitation was handled by the separate checker; preserve logs.

NEXT SELECTED TASK: test zero occurrence credit after applying this theorem.
Both earlier binding completed cycles are removed: the old four-cycle has
counts35443, the new five-cycle35453. The additional-share six-cycle survives.
For mean496 and C=0, rangeR<632 suffices for comparison<235. The old range602
uses C=83/3, so verify every edge under the new weights. Its validity at zero
credit is unknown. Compare BOTH profiles in the same new experiment.

The140/scripts/prepare_graph.py and evaluate_graph.py are prepared for the
old C=83/3 and protected by a proof-completion gate. They reproduce139's
removal set and both exact weight hashes before deletion, check both count
placements and orientations, and keep all inherited hypotheses. Derive
new141 files for zero credit; preserve140 sources/hashes. The full graph
has not been rerun in140. Small recognition checks passed.

Hypotheses still include earlier unproved count sums, hypothetical0123104
six-floor25, odd-length pair floor9, and extra share floors for the additional
profile. These calculations alone are not actual-snake upper bounds.
Even-length reasoning and the complete graph-to-snake proof remain separate.
The maintained interval191–235 and unresolved196 persist.

The exact native proof has18606 deductions,1397536 hints and4163 core inputs.
The two unused lower counters were replaced by empty endpoint counters;
all used meanings and the UNSAT CNF are unchanged. No extra cycle cuts or
endpoint-location assumptions were added. See independent-semantics audit.

Paper targeted revision140, no new definitions; last full136, next full146.
Compiler/PDF status must be read from140/data/latex-compilation.json.
Build objects remain local and their hashes are in receipts; Git retains
source and certificate evidence. Never mistake a local cached object for
an independently rebuilt dependency closure.

Milestone115 driver PID39044 was observed live at1095/1397 this round.
Verify its current command before any action; never duplicate it.104 stopped,
122 and129 completed. Lean needs>=1.5GiB free and at most2 existing Lean
processes; full graph needs>=3GiB and no other full-graph job. Preserve every
attempt and any new failures. Base commit8cc94035c72589d8d70edc31c576260d0cbef1d0.
"""
(R/'handoff/NEXT_AGENT_PROMPT.md').write_text(next_prompt,encoding='utf-8')
print('Saved completed local theorem and zero-credit continuation.')
