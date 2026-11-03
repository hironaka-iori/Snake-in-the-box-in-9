"""Save the credit obstruction and one selected empty-square continuation."""
from pathlib import Path
import json
H=Path(__file__).resolve().parents[1];R=H.parents[1]
q=json.loads((H/'data/Obstruction142-audit.json').read_text())
assert q['status']=='PASS' and len(q['axioms'])==10
note=r"""# Milestone 142: a zero-event cycle obstructs uniform credit

The proposed credit533/12 experiment failed. On the unchanged retained graph
of1,601,856 states and4,661,572 edges, the completed-share profile has mean
4406/9, potential range5377/9, and comparison9940859/42206>235. The target
mean3011/6 is not reached. The attaining cycle has nine edges and no credited
event. Its original weights are610,489,376,730,369,492,600,364,376, totaling4406.

## Consequence for the fixed graph

For any nonnegative uniform credit on the same occurrence indicator, this
cycle still caps the minimum mean at4406/9. For nonnegative mu,C,B,R,

\[
\mu\le4406/9\quad\Longrightarrow\quad
\frac{1098960+8\mu+BC+R}{4200+\mu}
\ge\frac{4962944}{21103}=235+\frac{3739}{21103}>235.
\]

Lean checked this implication, the exact tested comparison and its integer
consequence assuming a path-length comparison. It also checked that an
increase Delta in this cycle's total weight must exceed7478/227 even in
the zero-cost/zero-range case. Integer Delta must therefore be at least33.
These are fixed-model restrictions, not an impossibility result for all
empty-square arguments or all snakes. The cycle need not be realizable by
an actual snake. No optimal potential range is claimed.

## One next route: the empty-square share of012034

The bounded row review identifies one relevant additional floor. Of the
nine edges, six have canonical six-direction suffix012034 up to reversal.
Raising only this count-free share floor to18 increases their weights by
8,9,8,9,18,14, totaling66. Other additional share floors add nothing to this
particular cycle. Its new total would be4472.

A smaller immediate target is share13 for012034, over the existing five
internal centres and in the existing scale12 units. Floor12 adds30 and
leaves the total4436 obstructing even the zero-cost/zero-range test. Floor13
adds36 and raises the total to4442, passing that particular test. Both
arithmetic comparisons passed Lean. Floor13 does not establish a global
improvement, a sufficient potential, or the whole additional-share profile.
The existing conditional234 profile still calls for floor18 on this shape
and its other pending floors. The minimum sufficient floor13 concerns only
this saved cycle and this zero-cost/zero-range obstruction.

NEXT SELECTED TASK: seek a smaller count-free012034 share13 certificate
using a separate cap12 instance. Inspect the old share20 replay first;
preserve its exact sources and successful modules. Its last Check1 attempt
timed out after900s and no case7302 driver was live when checked this round.
Do not restart it automatically or change its input. The weaker target is
chosen to test whether a smaller proof can close an actual local theorem.
If successful, integrate only a fully checked actual-window result and
recompute the completed-share graph; do not assume the remaining cycles
or potential range improve sufficiently. Do not continue uniform-credit
tuning while the zero-event cycle remains unchanged.

## Evidence and limits

The evaluator checked all4,661,572 edge inequalities and an attaining cycle.
An independent bounded review reproduced40 original rows, nine zero cycle
slacks, adjacency and exact weights, using streams of at most1MiB. It verified
that the removal file is byte-identical to141. It did not repeat the complete
edge scan. The separate share-target review reconstructs the nine rows and
their alternative floors. Exact source pins, saved potentials and logs remain.

Ten Lean theorem reports passed, using only propext, Classical.choice and
Quot.sound. The graph potential has no complete Lean certificate here.
The cap from the saved graph cycle is the hypothesis of the checked general
arithmetic result. No complete actual-snake graph assembly is supplied.
Inherited count-sum hypotheses, hypothetical0123104 six-count floor25 and
the odd-length pair restriction remain. The additional-share profile also
retains its share-floor assumptions; its141 zero-credit comparison remains
551765/2348=235-15/2348<235. It was not rerun at positive credit.

The maintained interval191–235 is unchanged. The contributor235 proof has
an incomplete independent rebuild;196 and the exact optimum remain open.
No new unconditional global upper bound is claimed. The completed local
theorem from140 remains available with its actual-snake proof closure.

Paper targeted revision142 records the failed hypothesis and obstruction,
without new definitions or changes to authors/preamble/hyperlink settings.
Both paper copies match and source checks pass. The built-in compiler failed
before TeX, so no rebuilt PDF or visual layout verification is claimed.
Last full rewrite136; next146. The separate115 driver was observed live
at1158/1397. Observe its current process before acting; never duplicate it.
This round made progress by refuting a candidate and narrowing the next
share claim. Goal ACTIVE. The142 graph and arithmetic jobs have finished.
"""
(H/'MATHEMATICAL_NOTE.md').write_text(note,encoding='utf-8')
summary="""# Research update: milestone 142

Uniform credit533/12 failed: completed-share mean4406/9 and range5377/9
give comparison9940859/42206>235. A nine-edge cycle has zero credited
events. Lean checks that its mean cap prevents this uniform-credit method
from crossing235, even with zero credit cost and zero potential range.
The all-edge evaluator and bounded independent result review passed.

Next investigate one empty-square claim: count-free012034 share at least13
in the existing scale12 units. It is the smallest integer floor removing
this particular cycle's zero-cost/zero-range obstruction; no global bound
follows from that alone. Floor18 remains the requirement in the retained
additional-share profile, whose comparison551765/2348<235 is unchanged.
Use a separate cap12 proof attempt and preserve the old share20 replay.

Read milestones/142-retuned-occurrence-credit/MATHEMATICAL_NOTE.md and
data/share-targets.json. Ten Lean arithmetic statements passed. Full
graph-to-snake assembly and inherited hypotheses remain. Maintained
interval191–235 unchanged; no new unconditional global bound. Paper142
adds no definitions; source checks pass, PDF unavailable. The separate115
batch was observed live at1158/1397. Goal ACTIVE; this round is progress.
"""
(H/'README.md').write_text(summary,encoding='utf-8')
for name in ['README.md','COLLABORATION.md','RESEARCH_LEDGER.md','WORKSPACE.md','milestones/README.md','handoff/README.md','handoff/CURRENT_STATUS.md']:
 p=R/name;old=p.read_text(encoding='utf-8');assert not old.startswith('# Research update: milestone 142')
 p.write_text(summary+'\n## Earlier record\n\n'+old,encoding='utf-8')
prompt="""# Continue after milestone 142

Work in E:/Snake-in-a-box using tensai-bishoujo. Preserve the three authors,
paper preamble/hypersetup and unrelated .gitignore and milestone50 edits.
Only define necessary recurring notation. Edit the existing D:/Codex/
2026-10-13/new-chat/outputs/snake9_research.tex in place and keep the repo
paper copy identical. Fetch each round, retain exact evidence, stage only
a verified manifest, commit/push/verify. Goal ACTIVE; no exact optimum.

142 is complete. Do not restart its graph test. On4661572 edges, credit533/12
gives mean4406/9,range5377/9,comparison9940859/42206>235. The new9-cycle
has no credited events and base weights610,489,376,730,369,492,600,364,376.
Its mean caps all uniform credits on this fixed indicator. Lean checked
the lower comparison4962944/21103=235+3739/21103 even at zero cost/range.
Do not continue tuning this credit without changing the obstructing cycle.

NEXT SELECTED TASK: count-free012034 empty-square share13 (scale12), both
orientations, five internal centres, with no extra count assumptions. This
weak target is chosen because it removes this9-cycle's zero-cost/range
obstruction and may have a smaller proof. A separate cap12 native instance
is appropriate; preserve7302's oldcap19/share20 input and selected replay.
Last oldCheck1 timed out after900s; no7302process was live at142 inspection.
Never duplicate a live job. Check for a simpler existing certificate first.
Floor13 gives this cycle total4442 versus4436 for12. Floor18 adds66,total4472.
All gains come from012034; the other additional floors contribute zero on
these nine rows. Reversal must reverse the five local counts, not overwrite
the chronological last count used in the graph edge's120*last term.
See142/data/share-targets.json for exact rows and pins. Clipped6 means>=6.

The saved conditional234 profile still needs012034 share18 and its other
additional floors. 141's zero-credit comparison551765/2348<235 is retained.
A local13 theorem alone proves no global improvement. Only after actual
semantics, certificate, reversal and axiom audit should it enter completed
shares; then inspect the full graph and all remaining assumptions.

142's evaluator checked all edges; independent review checked40 rows,
cycle/slacks/potential range, unchanged removal bytes and arithmetic. It
did not repeat the full edge scan or establish optimal range. Ten Lean
arithmetic reports passed. Inherited count-sum claims, hypothetical0123104
six-floor25, odd-length pair restriction and full graph-to-snake assembly
remain. Maintained191–235, incomplete independent contributor235 rebuild,
and unresolved196 persist. Local140 actual theorem is already complete.

Paper targeted142, no new definitions, source checks pass. Builtin preview
compiler failed before TeX; no PDF claimed. Last full136; next146. Separate
115 driverPID39044 observed live at1158/1397; inspect current state, never
duplicate.104 stopped;122/129 complete. Lean gate>=1.5GiB free and at most
two existing Lean; fullgraph>=3GiB and no other fullgraph. Base commit
a42168ba3c810068bc9961849a6a9c6f7c618710. Exact evidence is retained.
"""
(R/'handoff/NEXT_AGENT_PROMPT.md').write_text(prompt,encoding='utf-8')
print('Saved142 result and the single empty-square share continuation.')
