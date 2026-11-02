"""Publish the completed checkpoint's exact remaining proof obligations."""
from pathlib import Path
import json
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
c=json.loads((HERE/'data/checkpoint.json').read_text())
assert c['status']=='PASS_ACTUAL_WEIGHT_CHARGE_AND_CONDITIONAL_UPPER_BOUND_CHAIN'
p=ROOT/'handoff/CURRENT_STATUS.md';s=p.read_text();a=s.index('## Milestone 97 checkpoint');b=s.index('## Result and evidence boundary',a)
block='''## Milestone 98 checkpoint

The complete actual edge-weight interpretation is checked for both profiles.
It includes all 505 geometric entries, 55 history-share rules, four
count-conditioned rules and their reversals, share 120, and the chosen
count-free floor. Every candidate bounds the same five-centre sum; they
combine by maximum. Saturation and the full direction/history/count key are
preserved. The five old credit-root ports are byte-identical to their sources.

The actual total charge is checked: the omitted endpoint/internal counts
save at least 21, and every share occurs at most five times. This proves
$W+4200m\\le1098960$ for $m\\ge9$. The completed profile has no unfinished
local-share premise. The conditional profile retains the five refutations
with floors (16,18,16,16,16).

The full-key walk and potential summation are checked in the same environment.
The completed upper235 assembly retains two reference-catalogue assumptions
and a slope-483, range-551 potential certificate on every defined graph row.
The conditional upper234 assembly retains the same two catalogue assumptions,
the five local refutations, and a slope-496, range-602 potential certificate.
These concrete potential/range certificates remain pending. No additional
weight-validity, boundary-saving or charge-budget premise remains.

Independent reconstruction matches all 4,947,008 saved full keys in 791 contexts,
both endpoint columns and both profile weights. This finite-array agreement
does not certify the potential on every row of the defined graph.

All 127 coverage classes and their actual-walk assembly remain checked from
milestone 97. The original case7302 target-20 replay remains stopped after its
900-second Check1 timeout, with 649 successful modules and unchanged evidence.
Any fresh target-18 proof must use separate files.

The maintained interval is $191\\le a(9)\\le235$, with 234 conditional. The
contributor upper-bound proof still lacks a complete independent rebuild.
Paper revision 96, its authors and hyperlink settings are unchanged; the next
scheduled full revision is 106. Use ordinary notation and define only
essential, substantially reused concepts.

'''
s=s[:a]+block+s[b:]
s=s.replace('The milestone 97 checkpoint\nabove supersedes them:','The milestone 98 checkpoint\nabove supersedes them:')
p.write_text(s)
p=ROOT/'handoff/NEXT_AGENT_PROMPT.md'
p.write_text('''# Assignment for the next researcher

Continue in `E:/Snake-in-a-box`. Read milestone 98's mathematical note,
checkpoint, proof summary and independent weight audit. The previous goal turn
made progress: the actual weights, total charge and final bound assembly are
checked. The exact optimum remains unresolved.

## Numerical status

The maintained interval is $191\\le a(9)\\le235$ edges. The upper bound uses
the inspected contributor theorem and archived audit; its complete independent
rebuild remains pending. The improvement to 234 is conditional. No 196 witness
or optimality proof was obtained here.

The completed profile has slope 483 and range 551 on the saved array. The
conditional profile with 012034 floor 18 has slope 496 and range 602. The latter
gives $4696m\\le1103530<4696\\cdot235$ after its hypotheses are supplied.
Milestone 97 proves that (16,18,16,16,16) is the least pending integer floor
vector inside the original target box for this fixed graph and boundary
argument. The range 602 is sufficient; its optimality is not asserted.

## Selected next task

Certify the potential inequalities and range bounds on the same defined graph
and exact weight functions used by PotentialAssembly98. Its final two theorems
state the necessary finite hypotheses precisely. Start with one representative
context and a verified efficient potential lookup before launching a large
batch. Existing balanced lookup arguments may avoid repeated long-list scans.

The conditional potential table is
`milestones/97-geometric-credit-integration/floor-sensitivity/012034-minimum/floor18-potential.i64.gz`.
Use the completed-profile evidence in milestone 93 for the other table. Preserve
raw state numbering and normalized ranges. Do not reuse the floor 20 range 600
potential as if it were the floor 18 certificate.

Check every code accepted by DefinedGraph92.diagramKeep, including conservative
extra rows. There are 791 recorded contexts and 127 shared acceptance classes,
but weights and endpoints depend on the full direction/history/count key.
An acceptance class or endpoint pair cannot replace that key. The independent
saved-array reconstruction in milestone 98 does not discharge these Lean
potential hypotheses.

Two reference-catalogue closures remain: AllRefuted6K235 and AllRefuted236.
The conditional profile also retains cases 7301,7302,7303,7307,7308 with
refutation caps 15,17,15,15,15. The completed profile has no unfinished local-share
premise. Keep these different scopes explicit.

## Completed interfaces

- CountConditionedCredits98 closes all four conditioned rules and share 120,
  with both direction and count reversal and the exact saturated intervals.
- CountFreeCredits98 supplies completedCredit and conditionalCredit with
  actual-key bounds. The 012034 conditional floor is 18, not the older 20.
- CombinedWeights98 defines weight floor q di code and bounds the actual
  weight by 120 times the entering singleton count plus the five-centre share.
- ActualGraphKeys98 preserves the full row key and both endpoints at the
  same index for every actual step. Coverage is already checked for all 127
  classes; the actual walk retains the two reference catalogues.
- GlobalCharge98 supplies the 21-count boundary saving, fivefold overlap and
  actual total-weight budget. It needs no extra graph or endpoint hypothesis.
- PotentialAssembly98 combines the charge with a potential on every defined
  row. completed_upper235 and conditional_upper234 retain exactly their stated
  local, reference and potential assumptions.

The namespace overlay in 98/build/support contains pinned copies of existing
proof objects. It resolves Lean's first-directory choice for nested module
namespaces. It is an ignored build cache, not new mathematical evidence.
Environment, provenance, exact source ports, compiler attempts and axiom audits
are saved. No complete clean dependency rebuild is claimed.

## Process and preservation

No restart of the completed 127-class batches is needed. Their old active
marker and waiting records are historical. Check real processes before any
restart. The original case7302 target-20 replay remains stopped after a
900-second Check1 timeout. Preserve its 649 successful modules, CNF, proof trace,
sources and completion record. A fresh target 18 attempt refutes share at most 17
and must have separate files. No speed improvement has been established.

Preserve unrelated changes to .gitignore and milestone 50's critical-family.json.
Fetch contributor changes before integration, stage only reviewed task files,
and verify the exact saved-file manifest after staging and pushing.

The paper remains revision 96, by Iori Hironaka, Tommy Ma and Steven Zhan.
Preserve all authors and hyperlink settings. The editor source is
`D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex`; the mirror is
`E:/Snake-in-a-box/paper/snake9_research.tex`. Edit and compile the existing
editor source when the next full revision is due at milestone 106. The earlier
compiler failure preceded source processing; no new PDF was verified.
Use ordinary notation and only essential, repeatedly used definitions.
''')
p=ROOT/'handoff/README.md';s=p.read_text()
i=s.index('The maintained interval')
s=s[:s.index('The current mathematical\ncheckpoint is')]+'''The current mathematical
checkpoint is [milestone 98](../milestones/98-concrete-weight-integration/README.md).
Its [mathematical note](../milestones/98-concrete-weight-integration/mathematical-note.md),
[checkpoint](../milestones/98-concrete-weight-integration/data/checkpoint.json)
and [manifest](../milestones/98-concrete-weight-integration/data/file-manifest.json)
record the complete actual-weight and charge integration and the exact
remaining upper-bound hypotheses.

'''+s[i:]
a=s.index('The next task is to instantiate');b=s.index('The original case7302',a)
s=s[:a]+'''Milestone 98 has completed the concrete count-dependent and count-free
weight interpretation, full-key walk, 21-count boundary saving, total charge,
and final numerical assembly. The next task is the potential and range
certificate on every row of the same defined graph. The two reference-catalogue
closures and five conditional local share proofs remain explicit.

'''+s[b:]
s=s.replace("Use milestone 97's manifest for this version.","Use milestone 98's manifest for this version.")
p.write_text(s)
print('UPDATED_MILESTONE98_HANDOVER')
