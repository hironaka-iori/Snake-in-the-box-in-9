"""Save the stronger numerical result and the exact next proof obligations."""
from pathlib import Path
import json
H=Path(__file__).resolve().parents[1];R=H.parents[1]
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
assert read(H/'broader/verification.json')['status']=='PASS_BROADER_CONDITIONS_NATIVE_RUP_REPLAY'
assert read(H/'data/paper-source-review.json')['status']=='PASS_TARGETED_PAPER_SOURCE_CHECKS'
note=r'''# A stronger share target on the critical eleven-window cycle

The new numerical certificate supports the following statement for a fitting
012032 window, with the corresponding reversed conditions in the opposite
orientation:

\[
\alpha_{r+1}=4,\quad \alpha_{r+2}\le4,\quad
\alpha_{r+3}=4,\quad \alpha_{r+4}\le5,\quad \alpha_{r+5}=3
\quad\Longrightarrow\quad
\sum_{j=1}^{5}\sigma_{12}(x_{r+j})\ge17.
\]

This is a target supported by a complete numerical contradiction. The broader
Lean interpretation, complete Lean replay and actual-snake composition are
unfinished. It must not be presented as a completed local snake theorem.

## Evidence and change of direction

One bounded query first tested share17 under actual second-plus-fourth count
at least10. It reached the90-second limit and stopped after92.453seconds.
Its exact input and incomplete output are archived. A timeout supplies
neither a theorem nor a counterexample.

The cycle audit explains why that restriction has limited relevance. All
four012032 windows on the saved eleven-cycle have exact pairs(4,5) or(5,4),
and the fourteen-cycle has no012032 window. A bonus restricted to pair sum
at least10 changes neither cycle. It could still improve a potential range
elsewhere; no general impossibility is asserted.

The next query used the actual critical context(4,4,4,5,3), corresponding to
edge2222339 and, after reversal, edge2220859. Its share-cap16 formula has
98,836clauses. The solver produced a contradiction, and a separate complete
unit-propagation replay verified30,305deductions and1,754,767references from
11,869retained input clauses. The solver run took25.156seconds. These are
measurements of this input and machine, not a speed comparison with the
earlier different queries.

Inspection found no retained or derived variable from the two lower-bound
counters at positions2and4. Removing their693registers gives an input with
97,443clauses and13,163variables. Every retained clause and deduction was
relabelled and replayed successfully without another solver invocation.
The same11,869compact clauses and every compact proof step are unchanged.
The broader conditions therefore need no second contradiction search or
second packed proof. Both input transformations and the compact identity
have independent audits.

The packed proof has290segments and10checkpoint groups. Its final empty
clause has original identifier190427 and tree key4398. Every transported
literal, ordered propagation reference and checkpoint was checked against
the native proof. These numerical checks do not replace Lean verification.

## Prepared sources and selected next step

The exact-count semantic export has97uncompiled modules. A pending adapter
adds three statements for arbitrary five count intervals, reversal, and
the exact critical context. The initial-tree pilot has34uncompiled modules,
covering2,095deductions and6,002references. The complete replay is estimated
from the generated dependency structure to require137modules. Full source
generation is guarded by acceptance of the initial-tree pilot.

The first semantic assembly draft had an incorrect argument order. It was
corrected by matching the already checked150assembly, before any153Lean
invocation. The original draft and source plan are preserved. No153Lean
module has yet passed or failed.

Do not compile two copies of the same contradiction. Prefer a broader
interpretation of the existing compact core, using the nine-counter table
and updated tags in `broader/meanings.json.gz` and the compact map in
`broader/mapping.json`. Preserve the exact-count sources and audits. The
broader model should conclude the same compact-core assignment statement;
its weaker bounds must appear explicitly in its local and actual-snake
theorems. Update the adapter inequalities and reversed bounds accordingly.
Then check one initial-tree pilot and one complete contradiction replay,
and compose both orientations. The existing exact-count adapter is a
source reference, not evidence that the broader transfer is checked.

The ongoing universal012032share16 job remains the immediate priority.
Inspect151's live progress and152's continuation before starting any Lean
process. The012301coordinator is held by152and must not be restarted.
Once152's queued final check succeeds, run its `scripts/audit_actual.py`
and use **`scripts/update_paper_after153.py`**, which matches the current
paper. Its older published paper-update script expects the previous paper
bytes. The successor also corrects the remaining-local-target list from
five to four. Run source checks and the built-in compiler after that edit.

## Consequence and limitations

For the profile imposing universal012032share16, establishing the exact
critical-context result and reversal would raise two eleven-cycle weights
by one, changing its total from5456to5458. The fourteen-cycle remains
unchanged. This is a conditional effect on saved finite-graph rows; it
does not establish a new potential, actual cycle realization, or global
upper bound. Broader conditions may apply to other rows, but their full
graph effect has not been computed.

The maintained interval remains191--235, using the contributor upper
theorem whose complete independent rebuild remains pending. The conditional
234profile retains its other local, reference and potential obligations.
The value196and the optimum remain unresolved.

All native inputs, incomplete output, numerical certificates and packed
transport are preserved in four byte-verified archives with46members.
Original files remain locally. The existing open TeX file and repository
copy match; authors, preamble and definitions are preserved. Static source
checks pass. The preview helper still fails before TeX processing, so no
new PDF or layout check is claimed. Last full paper revision146; next156.
The research goal remains active.
'''
(H/'MATHEMATICAL_NOTE.md').write_text(note,encoding='utf-8',newline='\n')
(H/'README.md').write_text('''# Milestone 153: critical-window share17 certificates

A complete numerical contradiction supports share at least17 for012032
under three exact counts and two upper bounds. Two unused lower-bound
counters were removed and the same proof was replayed; compact core and
proof steps are identical. No new solver run was needed for that extension.

Lean semantics, full Lean replay and actual-snake transfer remain pending.
The existing universal share16 replay is still the immediate priority.
The earlier high-pair query timed out and leaves the critical cycles unchanged.

Read MATHEMATICAL_NOTE.md, the three audit reports, broader/verification.json
and data/checkpoint.json. Preserve the exact-count sources and reuse one
contradiction proof for the broader interpretation. No new global bound.
''',encoding='utf-8',newline='\n')
update='''# Research update: milestone 153

A new complete numerical certificate targets012032share17 under counts
alpha1=4, alpha2<=4, alpha3=4, alpha4<=5, alpha5=3, with reversal. It has
30,305deductions and1,754,767references. Removal of two unused lower-bound
counters preserves the compact core and every compact proof step. Broader
Lean semantics and actual-snake transfer remain pending; reuse one replay.

The high-pair>=10test timed out and leaves both saved critical cycles
unchanged. The successful critical context instead raises two eleven-cycle
weights conditionally. No new global bound. Read153/MATHEMATICAL_NOTE.md.

The universal012032share16job and its152final continuation remain active;
inspect their live process state.147is temporarily held, not an active
compiler. After152completion, use update_paper_after153.py, not the older
paper-update script. Both paper copies now report153as numerical evidence;
source checks pass, while the preview helper fails before TeX. Goal ACTIVE.
Last full revision146; next156.

'''
for name in ['README.md','COLLABORATION.md','RESEARCH_LEDGER.md','WORKSPACE.md','milestones/README.md','handoff/README.md','handoff/CURRENT_STATUS.md']:
    p=R/name;p.write_bytes(update.encode()+p.read_bytes())
p=R/'handoff/NEXT_AGENT_PROMPT.md'
intro='''# Continue after milestone 153

Read milestones/153-pair-conditioned-share17/MATHEMATICAL_NOTE.md and its
checkpoint. First inspect the live151full replay and152final continuation;
do not duplicate either job or restart the held147coordinator. After the
queued final composition succeeds, run152/scripts/audit_actual.py and
152/scripts/update_paper_after153.py, then check and compile the open paper.
Publish a separate152completion manifest, preserving its running checkpoint.

The next mathematical proof target is the broader critical012032share17
certificate in153/broader. Its compact core and proof match the exact
certificate. Generate the broader nine-counter clause interpretation and
adapt the count/reversal bridge; check one bounded pilot and one full replay.
Do not compile the exact-count chain and then repeat the same contradiction
for broader counts. All153Lean sources remain uncompiled. No global bound
improvement is established. Last full paper revision146; next156.

Historical instructions follow; current statuses above take priority.

'''
p.write_bytes(intro.encode()+p.read_bytes())
print('SAVED153_RESEARCH_AND_CONTINUATION')
