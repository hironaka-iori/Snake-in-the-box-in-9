"""Publish the completed mathematical checkpoint and its remaining proof duties."""
from pathlib import Path
import json,re
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
c=json.loads((HERE/'data/checkpoint.json').read_text())
assert c['status']=='PASS_GEOMETRIC_HISTORY_CREDIT_INTEGRATION'
nw=len(c['checked_witness_classes']);ng=len(c['observed_geometry_classes']);na=c['new_lean_theorem_audits']
coverage=('All 127 numeric coverage classes and their final graph-walk assembly are checked under the two reference-catalogue premises.' if c['complete_numeric_coverage'] else f'The frozen snapshot records {nw}/127 witness classes and {ng}/127 geometry classes; complete assembly remains separate.')
latest=('Latest continuation: [milestone 97](milestones/97-geometric-credit-integration/README.md) integrates all 505 geometric credits and their maximum with the 55-rule history credit for actual snake windows. The finite-graph sensitivity certificates show that the least pending floor vector in the original integer target box is (16,18,16,16,16): the 012034 requirement drops from 20 to 18. The revised potential has slope 496, range 602 and strict margin 30 for conditional 234. '+coverage+' The global interval remains 191 through 235.')
priority=('Next research priority: instantiate the four count-conditioned rules and share-120 in the checked symbol-transfer interface; assemble the completed and conditional count-free profiles, using the weaker 012034 target 18. Then check the potential on the same defined graph. Preserve the original case7302 target-20 replay; any new target-18 refutation must use separate files. Keep the two reference-catalogue premises explicit. Paper revision 96 is unchanged; the next scheduled full revision is 106.')
for name in ['README.md','COLLABORATION.md']:
    p=ROOT/name;s=p.read_text()
    for prefix,value in [('Latest continuation:',latest),('Next research priority:',priority)]:
        s,n=re.subn('^'+re.escape(prefix)+'.*$',lambda m:value,s,count=1,flags=re.M);assert n==1
    p.write_text(s)
block=f'''## Milestone 97 checkpoint

All 505 nine-direction geometric table entries are connected to the actual
direction index, including 357 positive local bounds and 148 zero entries.
Their maximum with the completed 55-rule history credit bounds the same
five-centre share sum. The entire geometry catalogue, transfers and assembly
passed Lean in the current graph/history environment. Existing geometric
proof text changes only in import lines. The new symbol-share interface
preserves count saturation and reverses both directions and counts.

The fixed-graph optimisation now has a less demanding conditional target.
In case order 7301,7302,7303,7307,7308, the feasible integer floor vectors
inside the original target box are exactly (16,h,16,16,16), with h=18,19,20.
The h=18 potential passes all 4,947,008 edges at slope 496 and range 602,
giving strict margin 30 for the comparison below 235. At h=17, a 51-edge
walk and the mean-496 cycle obstruct every constant slope and global range.
The other four one-unit reductions have their own exact obstructions.
Monotonicity combines these into the complete integer-box classification.

The general arithmetic and monotonicity arguments are Lean-checked. Concrete
finite-graph witnesses and the potential table retain independently checked
integer evidence; their complete Lean replay remains pending. No universal
012034 share-18 theorem is claimed. Range 602 is sufficient, with no assertion
that it is the least potential range for that modified profile.

{coverage}

The checkpoint contains {na} theorem audits, including preserved local geometry
and auxiliary declarations. Paper revision 96 and both source copies are
unchanged. The interval remains $191\\le a(9)\\le235$, with 234 conditional.
The contributor upper-bound proof still lacks a complete independent rebuild.

The original case7302 replay remains stopped after Check1's 900-second timeout,
with 649 successful modules and unchanged original evidence. A new proof of
share at least 18 would refute share at most 17 and must be developed separately.
The next implementation task is the remaining concrete credit families and
their common weight, followed by the potential on the defined graph.

'''
p=ROOT/'handoff/CURRENT_STATUS.md';s=p.read_text();a=s.index('## Milestone 96 checkpoint');b=s.index('## Result and evidence boundary');s=s[:a]+block+s[b:]
anchor='The full proposed finite graph has';i=s.index(anchor)
s=s[:i]+'''Milestone 97 also verifies the weaker profile with 012034 floor 18, keeping
the other eight original target floors fixed. Its potential has slope 496 and
range 602, giving $4696m\\le1103530$ and conditional integer bound 234.
The least pending floor vector inside the original integer box is
$(16,18,16,16,16)$. The original stronger profile below remains valid as a
separate sufficient comparison with range 600.

'''+s[i:]
s=s.replace('| 012034 | 20 | Pending, case7302 |','| 012034 | 18 suffices; original target 20 | Pending; case7302 retains the stopped target-20 replay |')
p.write_text(s)
p=ROOT/'handoff/README.md';s=p.read_text();i=s.index('The latest manuscript and continuation checkpoint is')
s=s[:i]+'''The current mathematical checkpoint is
[milestone 97](../milestones/97-geometric-credit-integration/README.md).
Its [mathematical note](../milestones/97-geometric-credit-integration/mathematical-note.md)
states the completed geometric/history credit and the sharp conditional floor
requirements. The 012034 target can be lowered from 20 to 18. Its
[checkpoint](../milestones/97-geometric-credit-integration/data/checkpoint.json)
records the successful Lean assembly and current coverage-batch evidence.

'''+s[i:];s=s.replace('The latest manuscript and continuation checkpoint is','The latest manuscript checkpoint is',1);p.write_text(s)
p=ROOT/'handoff/NEXT_AGENT_PROMPT.md';s=p.read_text();a=s.index('Continue in');b=s.index('## Mathematical target',a)
s=s[:a]+'''Continue in `E:/Snake-in-a-box`. Read the current handover and milestone 97's
mathematical note, checkpoint, proof summary and remaining-credit-families audit.
Its floor-sensitivity/012034-minimum folder contains the sharp 18/17 threshold
and the complete integer-box consequence. Paper revision 96 remains current.

'''+s[b:]
a=s.index('## Selected next mathematical task');b=s.index('## Reuse completed proof interfaces',a)
s=s[:a]+'''## Selected next mathematical task

Reuse the completed geometric/history assembly in GeometricAssembly97. It
bounds all 505 geometric entries and their maximum with the 55 history rules
on the actual full key. The final theorem has only the snake and fitting-window
hypotheses. The entering-count term also has its checked actual-count bound.

SymbolCredit97 supplies the checked canonical and reversed count-symbol
transfers and the exact six-direction suffix/count-code adapters. Instantiate
the four historical count-conditioned refutations and share 120, preserving
their full intervals at saturated symbols. The remaining-credit-families
audit gives exact sources, receipts and safe import strategy. Avoid importing
the legacy ShareFrame or ambiguous SharePressure module names.

Assemble the completed count-free profile and a conditional profile using
012034 floor 18 rather than 20. The other pending floors remain 16. The original
partial catalogue expects the stronger 20 premise, so it cannot simply accept
a weaker certificate; give the new lookup its own exact interpretation.
Keep all unfinished local premises explicit. Combine candidates by maximum,
retaining their common centres r+4 through r+8 and the actual full edge key.

Then check the complete potential on the defined graph. The revised floor 18
potential has mean 496 and range 602 on the saved array, with margin 30 for 234.
Its complete Lean graph certificate is still pending. The saved old seven-edge
path retains deficit 600 and does not prove 602 is the optimal range.

The feasible integer vectors within the original pending-floor box are exactly
(16,h,16,16,16), h=18,19,20. The lower endpoint is supported by a full-edge
potential; the five failed adjacent profiles have cycle/path obstructions.
General monotonicity and comparison arithmetic are checked in PressureArithmetic97.
Concrete graph-witness membership and the complete potential retain their
computational scope until replayed in Lean.

For a new local proof attempt, share 18 requires refuting share at most 17.
Keep this fresh problem separate from case7302's old target 20 CNF, sources,
proof trace and timeout evidence. Do not restart the stopped old completion
helper merely because the next round begins. No speed improvement is assumed.

Use standard notation and define only essential, substantially reused concepts.
The next scheduled full paper revision is milestone 106.

'''+s[b:]
s=re.sub(r'The frozen milestone 96 checkpoint has \d+/127 witness classes, \d+/127 geometry',f'The frozen milestone 97 checkpoint has {nw}/127 witness classes, {ng}/127 geometry',s,count=1)
s=s.replace('Counts may have advanced.','Counts may have advanced. '+coverage,1)
a=s.index('The smallest proposed experiment is an isolated proof')
b=s.index('Case 7305 is complete and integrated:',a)
s=s[:a]+'''The original target-20 experiment is retained as a historical option. The
current argument needs only target 18. A fresh local refutation would exclude
share at most 17 and must preserve all original case7302 data and receipts.
See the milestone 97 sensitivity evidence before choosing a new proof run.

'''+s[b:]
if c['complete_numeric_coverage']:
    a=s.index('Witness session 13482 uses')
    b=s.index('Case 7302 stopped',a)
    s=s[:a]+'''Witness session 13482 and geometry session 23168 have completed their
127-class batches. CloseBatch assembles the full numeric coverage and actual
walk under the two reference-catalogue premises. Their final receipts are
preserved in milestone 97. No restart of these completed batches is needed.

'''+s[b:]
p.write_text(s)
p=ROOT/'milestones/README.md';s=p.read_text();i=s.index('- [Milestone 96:');assert '- [Milestone 97:' not in s
s=s[:i]+'- [Milestone 97: geometric credit integration and least pending floors](97-geometric-credit-integration/README.md). Complete 505-shape geometric/history credit; checked symbol transfers; sharp conditional floor vector (16,18,16,16,16) in the original integer target box. No new global bound.\n\n'+s[i:];p.write_text(s)
p=ROOT/'RESEARCH_LEDGER.md';s=p.read_text();assert '## Milestone 97:' not in s
s+='\n\n## Milestone 97: geometric integration and least pending floors\n\n3 November 2026, Japan time. '+latest+'\n\n'+priority+'\n';p.write_text(s)
(HERE/'README.md').write_text(f'''# Milestone 97: geometric integration and least pending floors

All 505 nine-direction geometric credits are connected to actual snake windows,
and their maximum with the 55 history-share rules bounds the same five-centre
share sum. The complete catalogue and its actual-index assembly have passed
Lean. The preserved local proofs, adapters and arithmetic have {na} theorem
audits, including auxiliary declarations and reused geometric instances.

The conditional 234 argument now needs only share 18 for 012034. A potential
with slope 496 and range 602 passes all 4,947,008 saved edges, giving margin 30.
Floor 17 is obstructed by a mean 496 cycle and a 51-edge walk. Combined with
four other obstructions, the feasible integer vectors inside the original
pending-floor box are exactly (16,h,16,16,16), h=18,19,20. The general arithmetic
and monotonicity are Lean-checked; the concrete graph certificates have
independent integer verification and are not yet a complete Lean graph proof.

Read the [mathematical note](mathematical-note.md), [proof summary](data/proof-summary.json),
[checkpoint](data/checkpoint.json), [remaining-credit audit](audit/remaining-credit-families.md),
and [sharp floor threshold](floor-sensitivity/012034-minimum/README.md).
The scripts preserve exact original/ported source bytes and successful
source/object/log/dependency hashes. Failed attempts, if any, remain saved.
Generated caches and build objects are excluded from the evidence manifest.

{coverage}

The interval remains $191\\le a(9)\\le235$ edges; 234 remains conditional.
No universal 012034 share 18 proof or proof of the exact optimum is supplied.
Paper revision 96 is unchanged; the next scheduled full revision is 106.
Case7302's original target 20 replay and its 649 successful modules are preserved.
The next task is to instantiate the remaining credit families, interpret the
weaker conditional profile, and check its potential on the same defined graph.
''')
print('UPDATED_MILESTONE97_HANDOVER',na,nw,ng,bool(c['complete_numeric_coverage']))
