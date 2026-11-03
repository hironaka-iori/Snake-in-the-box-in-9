"""Save the zero-credit result and the next completed-share parameter test."""
from pathlib import Path
import json
H=Path(__file__).resolve().parents[1];R=H.parents[1]
assert json.loads((H/'data/Comparison141-audit.json').read_text())['status']=='PASS'
note=r"""# Milestone 141: zero occurrence credit after the local exclusion

The proposed zero-credit test completed on 1,601,856 states and 4,661,572
retained edges. The checked five-count exclusion removed 200 edges from
milestone139. Both previous weight hashes and the entire predecessor
removal set were reproduced before the new rule was applied.

| Profile | Mean | Potential range | Comparison | Integer part |
|---|---:|---:|---:|---:|
| Completed share catalogue |3424/7|4159/7|7724271/32824|235|
| Additional share hypotheses |496|602|551765/2348|234|

The latter fraction equals235-15/2348. This recovers a conditional comparison
with integer part234. It does not improve the unconditional upper bound.
Even the completed-share profile retains inherited count hypotheses;
its name describes the share catalogue, not the status of the full proof.

## Verification and limitations

The evaluator checked every one of4,661,572 potential inequalities in each
profile and a cycle attaining each minimum mean. An independent review
reconstructed221 selected original rows, checked all200 new deletions,
cycle weights/adjacency/slacks, potential hashes/ranges and exact arithmetic.
It streamed original array data in chunks of at most1MiB. It did not repeat
the complete edge-inequality scan or establish minimal potential range.
The old conditional six-cycle survives; the new reported six-cycle is
different and has the same mean496. Both contain no counted event.

Lean checked eight statements: both exact comparisons, their integer
consequences assuming the path-length comparisons, the next credit's
intersection and range threshold, and the two-cycle arithmetic relaxation.
All reports use only propext, Classical.choice and Quot.sound. The finite
potential itself has not received a complete Lean certificate here.

The new local theorem from140 applies to arbitrary snakes and either parity.
The graph still inherits earlier unproved count-sum claims, the hypothetical
0123104 six-count floor25, the odd-length pair floor9, and additional share
floors in the second profile. Complete graph-to-snake assembly and any
required even-length argument remain separate. The maintained interval
191–235 and the unresolved optimum/196 are unchanged. The contributor235
upper proof still lacks a complete independent rebuild.

## Completed-share continuation

The new completed-profile seven-cycle has total weight3424 and two counted
low-pair suffix events. The old18-cycle survives, has no such event, and
has mean3011/6 under the current shared charges. Hence uniform credit C
leaves the two necessary mean restrictions

\[
\mu\le(3424+2C)/7,\qquad\mu\le3011/6.
\]

Their intersection is C=533/12. Under these two caps and nonnegative C,mu,R,
Lean proves the arithmetic lower bound

\[
\frac{1098960+8\mu+24C+R}{4200+\mu}\ge\frac{6624244}{28211}.
\]

Equality in this relaxation occurs at C=533/12,mu=3011/6,R=0. This no longer
prevents a comparison below235. It does not show that the graph has that
mean or admits zero potential range. Other cycles and actual range can
still prevent an improvement.

NEXT SELECTED TEST: use C=533/12 on the completed-share profile. At target
mean3011/6, a comparison below235 is equivalent to R<5341/6. The zero-credit
additional-share result remains the retained comparison for that profile.
There is no need to recompute it at the positive credit merely for symmetry.

Use integer weights12*w+533*event. If their exact mean is p/d and their
integer potential range is R_scaled, the comparison is

\[
\frac{12\cdot1098960d+8p+24\cdot533d+R_{\mathrm{scaled}}}
     {12\cdot4200d+p}.
\]

Actual mean and range divide by12. The target scaled mean is6022 and the
strict target scaled range is10682. Preserve both historical139 weight-hash
checks at their original scale3/credit83; only the new profile weights and
comparison change. Keep all inherited hypotheses and the checked140 gate.

## Saved records

The exact run, two potentials, removed indices and source snapshot are in
data/five-cycle-zero. Bounded independent reviews are in data/result-review.json
and data/zero-credit-source-review.json. The candidate parameter and saved-cycle
checks are in data/next-credit.json; arithmetic proof receipts are separate.
All exact sources and logs are retained. No141 calculation remains running.
The separate115 driver was observed live at1127/1397; inspect its actual
process before any action and never duplicate a live job.

The existing paper received targeted revision141 with no new definitions,
unchanged authors, preamble and hyperlink settings. Both copies match.
Source checks pass. The built-in compiler failed before TeX execution, so
no rebuilt PDF or layout check is claimed. Last full revision136; next146.
This round and the previous round made concrete progress. Goal ACTIVE.
"""
(H/'MATHEMATICAL_NOTE.md').write_text(note,encoding='utf-8')
summary="""# Research update: milestone 141

The zero-credit graph test completed. The checked five-count exclusion removes
200 edges;4,661,572 remain. Completed-share mean3424/7 and range4159/7 give
comparison7724271/32824>235. Additional-share mean496 and range602 give
551765/2348=235-15/2348<235, recovering the conditional integer comparison234.
No new unconditional upper bound is established; both profiles retain their
inherited count assumptions and graph-to-snake obligations.

All-edge checks passed in the evaluator. Independent saved-result review
checked221 original rows, all new deletions, cycles, potentials and arithmetic.
Lean checked eight arithmetic statements, including the integer consequences
and next parameter. A full finite-potential Lean proof remains separate.

Next use credit533/12 on the completed-share profile: the new seven-cycle
and surviving zero-event18-cycle meet at mean3011/6. A potential range below
5341/6 would suffice for comparison<235. Retain zero credit for the additional
profile. Read milestones/141-zero-credit-comparison/MATHEMATICAL_NOTE.md.

The maintained interval is191–235, with incomplete independent rebuilding
of the contributor upper proof. Paper update141 adds no definitions;
source checks pass, PDF unavailable. The separate115 batch was observed
live at1127/1397. Goal ACTIVE; this round is progress.
"""
(H/'README.md').write_text(summary,encoding='utf-8')
for name in ['README.md','COLLABORATION.md','RESEARCH_LEDGER.md','WORKSPACE.md','milestones/README.md','handoff/README.md','handoff/CURRENT_STATUS.md']:
 p=R/name;old=p.read_text(encoding='utf-8');assert not old.startswith('# Research update: milestone 141')
 p.write_text(summary+'\n## Earlier record\n\n'+old,encoding='utf-8')
prompt="""# Continue after milestone 141

Work in E:/Snake-in-a-box with the requested research skill. Preserve the
three authors, full paper preamble/hypersetup, and unrelated .gitignore and
milestone50 edits. Only define necessary recurring notation. Keep the
existing D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex editor and
paper/snake9_research.tex identical. Fetch, retain exact evidence, stage
only a verified manifest, commit/push/verify each round. Goal ACTIVE.

141's zero-credit full graph finished; do not restart it.4661572 edges remain
after200 deletions justified by140's checked theorem. Both profiles retain
inherited count assumptions. Completed shares:mu3424/7,range4159/7,
comparison7724271/32824>235. Additional shares:mu496,range602,
comparison551765/2348=235-15/2348<235, integer comparison234. This recovers
a conditional comparison; no new actual-snake bound or optimal range.

The evaluator checked all edges. Independent review checks221 selected
original rows, all200 deletions, cycles, potentials, hashes and arithmetic;
it does not repeat the all-edge scan. New conditional six-cycle differs
from139's, but both have mean496 and zero events. Eight Lean arithmetic
statements passed. Full graph-to-snake and Lean potential closure remain.

NEXT SELECTED TASK: completed-share credit C=533/12. Its new seven-cycle
has total3424 and2 events; a surviving zero-event18-cycle has current mean
3011/6. Their caps intersect at that credit and target mean. To make the
comparison<235 at this mean requires range<5341/6. Other cycles may
intervene. Preserve the successful additional-share zero-credit result;
only the completed profile needs this next optimisation calculation.

Derive new142 scripts from141's frozen evaluate_graph.py, whose SHA is in
preparation.json. New integer weights12*(base+shared)+533*event; actual mean
and range are scaled down by12. Comparison numerator12*1098960*d+8*p+
24*533*d+R_scaled; denominator12*4200*d+p. Target scaled mean6022 and
strict range bound10682. Retain BOTH old139 predecessor weight checks at
scale3/credit83. Keep140's actual weak-exclusion gate, both placements and
orientations, full edge checks, resource limits and exact snapshots.

The actual140 theorem is complete: canonical012032 with alternate counts
3,4,3 forces one intervening count>=6. The complete closure has123 modules;
no solver or replay needs restarting. Current141 seven-cycle IDs:
308563,3800424,2222339,147721,2200970,163743,2303752. See next-credit.json
for the old18-cycle survival and exact parameter algebra. The relaxation
minimum6624244/28211 is below235; it is not a claimed graph parameter optimum.

Inherited hypotheses: earlier unproved count sums, hypothetical0123104
six-floor25, odd-length pair floor9, and extra share floors for the second
profile. The maintained interval191–235, incomplete independent upper-proof
rebuild and unresolved196 persist. Do not infer even-length results silently.

Paper targeted revision141, source checks pass, builtin compiler failed
before TeX. No new definitions. Last full revision136; next full146.
Milestone115 PID39044 observed live at1127/1397; verify current command,
never duplicate.104 stopped;122/129 completed. No141 job remains running.
Lean gate>=1.5GiB free and at most2 existing Lean; fullgraph>=3GiB and no
other fullgraph. Base commit9f78ac76958cf146d1a90cd0a5743894a5f38284.
"""
(R/'handoff/NEXT_AGENT_PROMPT.md').write_text(prompt,encoding='utf-8')
print('Saved141 result and the completed-share credit continuation.')
