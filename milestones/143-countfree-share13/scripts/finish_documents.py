"""Save the superseded share13 attempt and the sharper range obstruction."""
from pathlib import Path
import json
H=Path(__file__).resolve().parents[1];R=H.parents[1]
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
assert read(H/'data/Range143-audit.json')['status']=='PASS'
assert read(H/'data/intentional-stop.json')['checked_modules']==23
note=r"""# Milestone 143: account for potential range when selecting a share target

The zero-range test in142 selected count-free012034 share13. A stronger
test now rules out every floor at most14 for the existing comparison,
even with an optimal potential and any nonnegative uniform occurrence
credit on the same indicator. This changes the next-task priority.

## Checked obstruction

At floor14, the saved zero-event nine-cycle has weights
614,494,376,734,374,492,614,374,376, totaling4448. Its last five edges
have total2230. Summing potential inequalities gives

\[
\mu\le4448/9,\qquad R\ge5\mu-2230.
\]

All cycle weights can only decrease at smaller floors. Both restrictions
therefore hold for every floor at most14. For nonnegative mu,C,B, Lean proves

\[
\frac{1098960+8\mu+BC+R}{4200+\mu}
\ge\frac{4964197}{21124}=235+\frac{57}{21124}>235.
\]

This assumes the same other weights, retained edges and occurrence indicator.
The graph usesB=24. New exclusions, other share rules or different accounting
can change the result. Seven Lean theorem reports passed, including both
telescoping calculations and comparison implications. All audited axioms are
propext, Classical.choice and Quot.sound.

The exact cycle-only comparison first drops below235 at floor15:
mean4454/9, minimum cycle-only range2173/9, comparison235-1245/42254.
At floor18 the values are4472/9,2182/9,235-2661/21136. Explicit potentials
on the nine-cycle make every edge inequality an equality; a subwalk attains
each stated range. No extension to the complete graph or optimal full-graph
range is asserted. No full graph evaluation was rerun in143.

## Preserved share13 attempt

The separate cap12 query used012034, five bounds[0,21], radius4, resolution12
and no added cycle cuts. Its10,616 variables and88,038 clauses were rebuilt
independently. The trimmed certificate has29,165 deductions,1,699,457 hints
and10,078 original clauses. Two independent positive-hint replays reached
the empty clause. Ordinary base four/six-cycle clauses remain present.

The share encoding preserves35 centre-neighbor incidences over32 distinct
neighbor vertices. The independent audit reconstructed square sets, threshold
rounding, totalizers, every saved meaning/tag, and full/core bytes and pins.
This establishes the saved Boolean contradiction, with no actual-snake
share13 theorem yet.

The Lean export has231 planned modules;23 passed before intentional
termination after 23 completed modules, when the stronger obstruction superseded13.
Every completed receipt, input, proof, generated source and log is preserved.
The stale replay-progress file records its last RUNNING observation;
data/intentional-stop.json is the authoritative stop record. No143 driver
remains. Full semantic interpretation, replay, coordinate mapping and reversal
must pass before claiming the local theorem. The old7302 share20 attempt
was read only and remains unchanged.

## Selected continuation

Target count-free012034 share18 directly, in scale12 units, for every fitting
six-transition window and its reversal. Use the same five broad bounds[0,21]
in a SEPARATE cap17 query. Preserve cap12 and oldcap19/share20 evidence.

Floor15 is only the first floor not excluded by this cycle and walk. Floor18
is already required in the retained additional-share profile, whose comparison
is551765/2348<235. Proving18 would replace this one share hypothesis with an
actual local theorem. Other share/count hypotheses, hypothetical0123104
six-floor25, the odd-length restriction and graph-to-snake assembly remain.

For a new export, derive variable widths and slots from its own proof. Verify
any variable/clause-ID renaming. Do not reuse cap12 hashes as cap17 evidence.
Do not resume the stopped13 replay without a separate mathematical use.

Maintained interval191–235 unchanged; contributor upper proof independent
rebuild incomplete;196 and optimum unresolved. Paper targeted143 preserves
authors/preamble/hypersetup and adds no definitions. Source checks pass;
builtin compilation fails before TeX, with no rebuilt PDF/layout claim.
Last full rewrite136; next146. Separate115 was observed live at1203/1397,
and its driver was not interrupted. All143 jobs are complete or stopped.
Goal ACTIVE. This round made progress through the stronger obstruction.
"""
(H/'MATHEMATICAL_NOTE.md').write_text(note,encoding='utf-8')
summary="""# Research update: milestone 143

A nine-cycle and its five-edge subwalk rule out012034 share floors at most14
for this comparison, even with an optimal potential and any nonnegative
uniform occurrence credit. Lean checks the lower comparison235+57/21124.
Floor15 survives this cycle test only; no full-graph sufficiency follows.
Next target the existing count-free share18 requirement in a separatecap17
query. The retained conditional comparison551765/2348 is unchanged.

The weaker share13 Boolean contradiction passed two complete replays:
29165 deductions,1699457 hints. Its231-module Lean export is preserved;
23 passed before intentional termination when the range obstruction
superseded13. No actual share13 theorem is claimed. Old share20 untouched.
Read milestones/143-countfree-share13/MATHEMATICAL_NOTE.md and its stop record.

Seven new Lean arithmetic reports passed. Maintained interval191–235
unchanged; other hypotheses and actual-snake assembly remain. Paper143
adds no definitions; source checks pass, PDF unavailable. Separate115
observed live at1203/1397; no143 job running. Goal ACTIVE, round is progress.
"""
(H/'README.md').write_text(summary,encoding='utf-8')
for name in ['README.md','COLLABORATION.md','RESEARCH_LEDGER.md','WORKSPACE.md','milestones/README.md','handoff/README.md','handoff/CURRENT_STATUS.md']:
 p=R/name;old=p.read_text(encoding='utf-8');assert not old.startswith('# Research update: milestone 143')
 p.write_text(summary+'\n## Earlier record\n\n'+old,encoding='utf-8')
prompt="""# Continue after milestone 143

Use E:/Snake-in-a-box and tensai-bishoujo. Preserve three authors, the paper
preamble/hypersetup, existing D:/Codex/2026-10-13/new-chat/outputs/
snake9_research.tex editor and its repo mirror, unrelated .gitignore and
milestone50 edits. Define only necessary recurring notation. Fetch, retain
exact evidence, stage a verified manifest, commit/push/verify each round.
Goal ACTIVE; optimum and196 unresolved.

142 disproved credit533/12. 143 sharpens the next share target using range:
at012034 floor14 the zero-event9-cycle totals4448 and its last5 edges total
2230. Hence mu<=4448/9,R>=5mu-2230. Lean proves comparison>=4964197/21124
=235+57/21124 for any nonnegative occurrence cost. Smaller floors decrease
these weights. This rules out every floor<=14 in the unchanged model.
Floor15 is first not excluded by this cycle+walk; not globally sufficient.

NEXT SELECTED TASK: count-free012034 share18, resolution12, five internal
centres, both orientations. Build a SEPARATE cap17 query with five broad
[0,21] count bounds, radius4, no added cuts. Target18 because it is already
required by the retained conditional234 profile. Complete the certificate,
semantics, actual-window mapping, reversal and axiom audit before updating
completed shares. Other share/count and graph-to-snake hypotheses remain.

143 cap12/share13:10616vars,88038clauses,10078coreclauses,29165deductions,
1699457hints; two full RUP replays passed. Generated Lean plan231modules,
23 passed. Driver26336 intentionally terminated after 23 completed modules, following the
new obstruction. data/intentional-stop.json overrides stale RUNNING status;
do not restart automatically. Preserve all sources/objects/logs. Old7302
cap19/share20 unchanged; its historicalCheck1 timed out after900s.

For new18 work,143/scripts/prepare.py,certify_base.py,export_lean.py provide
the pipeline. Use new paths/namespace/pins and actual proof widths; never
overwrite12 or20 evidence. Encoder28/scripts/tagged_share.py preserves35
incidences on32 neighbors. Core tags and cap rounding matter. The general
share bridge supports actual snakes/reversal; the new full chain must pass.
Independent143 native audit reconstructs base and share encodings.

143 Range143 has7 checked reports; cycle-only potentials attain the saved
subwalk range. No fullgraph range optimum/new fullgraph calculation. Retained
conditional551765/2348<235 and maintained191–235 unchanged. Contributor235
independent rebuild incomplete. Inherited sums, hypothetical0123104floor25,
odd-pair9, extra share premises and actual-snake graph assembly remain.

Paper targeted143; source checks pass, no definitions added. Builtin compiler
failed before TeX; no PDF. Last full136; next146. Separate115PID39044 observed
live1203/1397; inspect current command, never duplicate.104 stopped;122/129
complete. Lean gate>=1.5GiB free and<=2 existing Lean; fullgraph>=3GiB and
no other fullgraph. Base d29e9db3e5590942fbd4ba4a966e89b1f65870ab.
"""
(R/'handoff/NEXT_AGENT_PROMPT.md').write_text(prompt,encoding='utf-8')
print('Saved143 range obstruction, stopped replay and next share18 target.')
