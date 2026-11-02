"""Publish milestone 93's frozen evidence level and continuation instructions."""
from pathlib import Path
import json,re
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
c=json.loads((HERE/'data/checkpoint.json').read_text())
nw=len(c['checked_witness_classes']);ng=len(c['observed_geometry_classes']);nc=c['case7302_distinct_successful_modules']
latest=("Latest continuation: [milestone 93 checkpoint](milestones/93-defined-graph-potential/README.md) "
        "adds seven Lean comparison audits. Independently checked cycle and path certificates prove joint optimality "
        "of the slope and global potential range on each of the three fixed weighted array graphs. Their integer "
        "comparisons remain 235, 235 and conditionally 234. "
        f"The snapshot records {nw}/127 witness classes, {ng}/127 geometric classes and {nc} successful case7302 modules. "
        "The witness and geometry batches continue; case7302 stopped after a 900-second Check1 timeout. "
        "Bounds remain 191 through 235, with 234 conditional; paper revision 86 is unchanged.")
priority=("Next research priority: prove the exact key-dependent five-centre credit bound, especially complete "
          "coverage of compatible eleven-transition words for all 55 history share rules. Continue the existing witness "
          "and geometry batches. The recorded fixed-model comparisons cannot be improved by changing only the constant "
          "slope and global potential range. The defined graph still needs its complete weight and potential checks. "
          "For case7302, test one isolated replay segment before changing or restarting the timed-out six-segment check. "
          "Keep the two reference-catalogue premises and all five pending local shares explicit.")
for name in ['README.md','COLLABORATION.md']:
    p=ROOT/name;s=p.read_text();s,n=re.subn(r'^Latest continuation:.*$',latest,s,count=1,flags=re.M);assert n==1
    if name=='README.md':s,n=re.subn(r'^Next research priority:.*$',priority,s,count=1,flags=re.M);assert n==1
    else:s=s.replace('Checkpoint: 2 November 2026.','Checkpoint: 3 November 2026.',1)
    p.write_text(s)
block=f'''## Milestone 93 checkpoint

Seven new Lean audits prove rational path telescoping, the path-deficit inequality,
the cycle slope ceiling and joint slope/range comparison, including three conditional
numerical applications. Exact independent checks verify all 4,947,008 edge inequalities
for each profile and 73 witness occurrences. The best fixed-model comparison fractions
are $157625/669$, $20965613/89059$ and $137941/587$, giving integer comparisons
235, 235 and conditionally 234. Concrete graph embedding remains computational evidence.

The new [mathematical note](../milestones/93-defined-graph-potential/mathematical-note.md)
shows that changing only the constant slope and global potential range cannot improve
these fractions on the unchanged weighted graphs with the same boundary budget.
The selected continuation is the exact five-centre credit theorem, especially complete
compatible variants for the 55 history share rules. The defined graph must have its
own full weight and potential check; external-array certificates do not transfer by name.

The frozen snapshot has {nw}/127 checked witness classes, {ng}/127 checked geometry
classes and {nc} successful case7302 modules. Witness session 13482 and geometry
session 23168 continue. The replay in session 14427 ended at a 900-second Check1
timeout. Its confirmed orphan compiler was stopped, with evidence preserved.
The next replay experiment is one isolated segment, without changing the original
source or data. Inspect actual processes before any restart.

The interval remains $191\\le a(9)\\le235$ edges, with 234 conditional. The upper
bound uses the inspected contributor theorem and saved audit; its complete independent
rebuild remains pending. Paper revision 86, all three authors and hyperlink settings
are unchanged. The next scheduled paper revision is milestone 96.

Earlier entries below retain their historical scope. Use the milestone 93 checkpoint
for the current frozen evidence and process observations.

'''
p=ROOT/'handoff/CURRENT_STATUS.md';s=p.read_text();a=s.index('## Milestone 92 checkpoint');b=s.index('## Result and evidence boundary');s=s[:a]+block+s[b:];p.write_text(s)
p=ROOT/'handoff/README.md';s=p.read_text();a=s.index('The current checkpoint is');b=s.index('Milestone 91 completed',a)
s=s[:a]+'''The current checkpoint is
[milestone 93](../milestones/93-defined-graph-potential/README.md), with seven
Lean comparison audits and independent numerical cycle/path certificates for three
fixed weighted graphs. Its [checkpoint](../milestones/93-defined-graph-potential/data/checkpoint.json)
and [manifest](../milestones/93-defined-graph-potential/data/file-manifest.json)
preserve exact evidence, continuing witness/geometry observations and the stopped
case7302 timeout. The selected next task is the key-dependent credit-to-share proof.

[Milestone 92](../milestones/92-full-witness-batch/README.md) supplies the checked
source-compatible context assignment, defined graph and generated witness batch.
Reuse those sources and matching successful receipts.

'''+s[b:];p.write_text(s)
p=ROOT/'milestones/README.md';s=p.read_text();pos=s.index('- [Milestone 92:');s=s[:pos]+'''- [Milestone 93: joint slope and range comparison](93-defined-graph-potential/README.md). Seven new Lean audits; exact independent certificates show that all three fixed weighted graphs already attain their best constant-slope/global-range comparisons. No new snake bound. Case 7302 stopped after a timeout; witness and geometry batches continue.

'''+s[pos:];p.write_text(s)
p=ROOT/'RESEARCH_LEDGER.md';s=p.read_text();assert '## Milestone 93:' not in s
s+='\n\n## Milestone 93: joint slope and range comparison\n\n3 November 2026, Japan time. '+latest+'\n\n'+priority+'\n\n'
s+='The new comparison is checked in Lean under explicit graph-witness hypotheses. Concrete embedding and every array potential inequality were checked numerically by two implementations. This does not discharge the actual-snake credit theorem or the complete potential check on possible extra diagram rows. All original paper bytes are preserved. The exact optimum remains unresolved.\n';p.write_text(s)
p=ROOT/'handoff/NEXT_AGENT_PROMPT.md'
p.write_text(f'''# Assignment for the next researcher

Continue in `E:/Snake-in-a-box`. Read the current handover, milestone 93's
mathematical note, checkpoint and two independent audits, then milestone 92's
context-assignment and defined-graph interfaces. Paper revision 86 is current.

## Mathematical target and evidence boundary

The maintained interval is $191\\le a(9)\\le235$ edges. The 235 upper bound
uses the inspected contributor theorem and saved audit; its full independent
rebuild remains pending. The target 234 is conditional. No 196-edge witness
or optimality proof has been established here. Keep the exact optimum open.

Continue the empty-square charging route. Alternate numerical strengthening
with completion of the proof obligations. Distinguish local solver models,
refutations, Lean local theorems, finite-graph computations and universal bounds.

## What milestone 93 changes

Seven Lean audits prove the cycle-and-path comparison. A cycle of mean $M$
forces every feasible slope $\\mu\\le M$. A path of length $k$ and weight $C$
forces range $\\rho\\ge k\\mu-C$. When $R=kM-C$ and
$k+8\\le(1098960+8M+R)/(4200+M)$, the baseline pair is jointly optimal
for this fixed graph, weight function and boundary budget.

Independent exact calculations confirm the following finite-array comparisons:

| Profile | Mean | Normalized range | Path length / weight | Best comparison |
| --- | ---: | ---: | --- | ---: |
| Completed floors | $483$ | $551$ | $9/3796$ | $157625/669$ |
| Additional assumed 012034 floor 20 | $9259/19$ | $11301/19$ | $31/14512$ | $20965613/89059$ |
| Full conditional profile | $496$ | $600$ | $7/2872$ | $137941/587$ |

Do not spend the next round reoptimizing only these two parameters on unchanged
weights. Stronger local credits, actual-snake restrictions, stronger boundary
accounting or endpoint-specific bounds can change this conclusion's hypotheses.
Concrete witness embedding is computational evidence; the Lean applications
retain it as hypotheses. Potential feasibility on possible extra diagram rows
has not been established.

## Selected next mathematical task

Prove the exact actual-key credit inequality

$$
L(d_r,q_r,c_r)\\le\\sum_{{i=0}}^4\\operatorname{{coreShare}}(12,p,r+i+4).
$$

Start with complete compatible eleven-transition variants for the 55 history
share rules. The three history exclusions are already checked; that is a
different statement. Forty-seven of the 58 total history rules carry a
`variants` field; a missing field does not prove uniqueness. All variants of
each share signature need coverage and the applicable five-centre bound.

Use the precise offsets in `93-defined-graph-potential/audit/weight-bridge-plan.md`.
The actual eleven-word begins at $r-2$, share centres have offsets 6 through 10,
and six-count position $k$ corresponds to offset $5+k$. Symbol 6 represents
the interval $[6,21]$. Alternative credits bound the same share total and
combine by maximum. Keep the full key $(d,q,c)$: equal endpoints or acceptance
classes do not imply equal credits. The exact edge weight is
$120(c\\bmod6+1)+L(d,q,c)$.

Then check every accepted-code block of the defined graph with its own exact
weights and potential. Raw state numbers range below 1,601,856. Missing block
lookups reject. There are 791 compatible contexts and 127 acceptance classes.
Use the key equality in `Assembly87.actual_saved_edge` when selecting credits;
the endpoint-only conclusion of `defined_actual_walk` is insufficient alone.

## Reuse completed proof interfaces

Milestones 77–79 check direction/history states, encoded counts, saturation and
the ten interval filters. Milestone 81 checks all forty recovered short filters.
Milestone 84 closes the three history exclusions. Milestone 85 checks the exact
1,378-key reference union under `AllRefuted6K235` and `AllRefuted236`; their
compatible closed dependencies still need restoration or rebuilding.

Milestone 87 supplies numeric retention and conditional saved-walk assembly.
Milestone 88 supplies generic witnessed rejection and coverage. Milestones 89–92
materialize and check the shared geometric covers and context-specific witnesses.
The context selector is complete over 37,875 positions, including three overrides.
The defined graph avoids an external-array identity only when later weights and
potentials are checked on that same graph. Preserve all full keys and leading
history witnesses: class 85 has two and class 89 has one, each at position 0.

## Active jobs and local-share replay

The frozen milestone 93 checkpoint has {nw}/127 witness classes, {ng}/127 geometry
classes and {nc} successful case7302 modules. Counts may have advanced.
Witness session 13482 uses the unchanged milestone 92 checker with
`--classes all --wait-for-geometry`. Geometry session 23168 continues separately.
Inspect live processes and active records before any restart. The witness
runner has a memory gate and preserves an interrupted active job's lock.

Case 7302 stopped at `LocalWindowUnsat/ShareWindow7302/Check1` after 900 seconds.
Its confirmed orphan compiler was stopped and failure evidence preserved.
Do not rerun the old unique-resume helper unchanged: it assumes a prior
Check66 failure. Do not regenerate data or invalidate existing successful proofs.
The smallest proposed experiment is an isolated proof of the original segment 1
statement importing only Data1, with a fresh helper name. Preserve Check1 and
its six statements until that pilot is measured. In particular, segment 4
includes both its check and checkpoint equality. See the replay audit.

Case 7305 is complete and integrated: 465 source modules and 100 local audits;
the combined catalogue has 35 audits. Completed target cases are 7300, 7304, 7305,
7306. Pending target cases remain 7301, 7302, 7303, 7307, 7308. The additional 012034
floor 20 alone still gives integer comparison 235. A final local theorem needs
composition, geometry, reversal and source/axiom audit, followed by archival,
restoration, integration and recomputation. Partial replay does not suffice.

## Documents and reproducibility

Preserve authors Iori Hironaka, Tommy Ma and Steven Zhan and all hyperlink settings.
Paper revision 86 has130 statements. The next full rewrite is scheduled for 96.
The editor source is `D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex`;
its repository mirror is `paper/snake9_research.tex`. Edit the existing editor
source in place when due, synchronize its mirror and use the built-in compiler.
The previous compiler failure preceded source processing; no new PDF was verified.

Use Lean 4.19.0 and the pinned inherited environment. Preserve exact source,
object, receipt and log hashes. Reused dependency objects do not constitute
a complete clean rebuild. Fetch before integrating contributor changes,
preserve unrelated working-tree modifications and stage only reviewed files.
Save evidence, unresolved hypotheses and actual process state after each round.
''')
print('UPDATED_SEVEN_HANDOVER_FILES',nw,ng,nc)
