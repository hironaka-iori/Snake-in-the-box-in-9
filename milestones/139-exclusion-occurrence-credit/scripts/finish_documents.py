from pathlib import Path
import json,hashlib
H=Path('milestones/139-exclusion-occurrence-credit');R=H.resolve().parents[1]
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
log='Compiler helper failed: exec failed: unsupported operation: windows unelevated restricted-token sandbox cannot enforce split writable root sets directly; refusing to run unsandboxed\nFalling back to bundled Tectonic.\n'
(H/'data/latex-compilation.json').write_text(json.dumps(dict(status='INFRASTRUCTURE_FAILURE_BEFORE_TEX',source_sha256=sha(R/'paper/snake9_research.tex'),log=log,pdf_rebuilt=False),indent=2)+'\n')
p=H/'data/paper-revision.json';j=json.loads(p.read_text());j['status']='SAVED_SOURCE_CHECKED_COMPILER_UNAVAILABLE';p.write_text(json.dumps(j,indent=2)+'\n')
note=r"""# Milestone139: limits of uniform occurrence credit after exclusion

## Result

The exact graph experiment completed on1,601,856 states and4,661,772 retained
edges. The full-nine theorem removed exactly edge992157. Uniform suffix
credit83/3 was applied to8,846 exactly recognized low-pair events. Count
symbols6 were excluded from this event test because they mean at least6.

| Weight profile | Mean | Potential range | Comparison | Attaining cycle |
|---|---:|---:|---:|---:|
| Completed shares |2446/5|2973/5|5520661/23446|5 edges, zero credited events|
| Additional shares |496|602|552097/2348|6 edges, zero credited events|

Both comparisons exceed235. Both profiles retain all milestone131
hypotheses: inherited unproved count-sum claims, the hypothetical0123104
six-count floor25, and the pair floor9 for odd-length snakes. The additional
profile also assumes its share floors. These are conditional finite-model
results, not new actual-snake upper bounds. In particular, an even-length
bound does not follow automatically from this odd-length model.

The evaluator reproduced the immediate predecessor's complete removal set
and both weight hashes, checked every new edge potential inequality and
an attaining cycle for each mean. An independent review reconstructed
40 selected original rows, cycle weights, adjacency and zero potential
slack, and checked source hashes, predecessor counts, potential arrays,
ranges and comparison arithmetic. It did not repeat the all-edge scan.
No full finite-potential Lean certificate was generated this round.

## Checked logic and optimisation limit

Credit139 proves that both clipped counts below6 certify their actual
values, and that distinct suffix starts counted by this condition inject
into milestone137's actual low-pair starts. Therefore this subset also
contains at most24 starts. The result applies to either path parity;
the additional odd-length restriction belongs to the comparison graph.

The new five-cycle receives no credit. Its completed-profile mean therefore
stays2446/5 for every uniform credit C. The old four-cycle has mean488+C/2.
Using these two upper restrictions on the graph mean and allowing any
nonnegative potential range gives

\[
\frac{1098960+8\mu+24C+R}{4200+\mu}
\ge\frac{2757328}{11723}>235.
\]

The arithmetic relaxation attains equality at C=12/5, mu=2446/5, R=0.
This is a proved optimum of the displayed relaxation, not evidence of a
graph potential with zero range or of the best actual credit parameter.

Obstruction139 proves more generally that the five-cycle mean cap prevents
this comparison from reaching235 for any nonnegative credit, allowance
and range. The zero-event six-cycle similarly keeps the additional-profile
mean at most496 and prevents its comparison from reaching234. OptimalCredit139
checks the sharper completed-profile relaxation above.

All three new modules passed Lean, with six axiom reports in total using
only propext, Classical.choice and Quot.sound. The graph means themselves
are supported by exact computation and the saved independent review;
the obstruction theorems explicitly take the relevant mean caps as premises.

## New critical window and selected continuation

The completed five-cycle consists of edges308566,3806548,2195856,163743,
2303753. Its first row has directions012034054 and six counts335453.
Its canonical suffix is012032 with five counts(3,5,4,5,3). The relevant
pair sum is10, so the proved endpoint consequence for pair sum<=9 does
not cover it.

A fresh validation of the same135 distinct saved actual snakes checked
2,447,698 unordered vertex pairs and25,479 internal counts. It found one
full-nine shape occurrence and136 suffix-shape occurrences, but no exact
required count match in either case. Both whole-path orientations were
tested. This supplies no exclusion proof and no counterexample.

NEXT SELECTED TASK: a bounded actual-path feasibility test for the symmetric
six-transition window012032 with exact counts(3,5,4,5,3), beginning with
the necessary full-cube model and ordinary cycle cuts. If it is impossible,
certify the contradiction and its actual-snake interpretation. If an actual
snake realizes it, keep the witness and test a stronger local charge or
endpoint consequence only when the witness permits it. Do not assume the
count pattern forces an endpoint. The original full-nine row is a narrower
fallback if the shorter pattern is feasible.

The pending milestone138 short cap(3,3,3,5,2) has no match on either new
attaining cycle and is not the selected next calculation. Do not launch
a large proof batch solely because that older certificate is available.

## Files and paper

data/exclusion-credit83 holds the exact script snapshot, complete graph
result, both potentials, removed indices and logs. data/result-review.json
and audit/check_result.py hold the independent saved-result review.
The three Lean receipts, exact compiler inputs, outputs and objects are
saved alongside the source. All statuses and hashes are indexed by the
checkpoint manifest.

The existing paper received targeted update139, with unchanged authors and
preamble and no new definitions. Source checks pass. The built-in compiler
again failed before TeX execution; no updated PDF or visual check is claimed.
Last full revision136; next full revision146.

The maintained interval remains191–235 with the documented incomplete
independent upper-proof rebuild. The optimum and196 remain open. The
milestone115 driver was observed live at1056/1397; never duplicate a live job.
The previous goal turn and this round both made concrete progress.
"""
(H/'MATHEMATICAL_NOTE.md').write_text(note,encoding='utf-8')
(H/'README.md').write_text("""# Milestone139: the new zero-credit cycles

The full-nine exclusion and uniform credit83/3 were tested together.
Both exact finite profiles completed and received an independent saved-result
review. Their means are2446/5 and496; each has an attaining cycle with zero
credited events. Both comparisons remain above235.

Lean checked the program's clipped-count occurrence subset, the resulting
24-start bound, both uniform-credit obstructions, and the exact optimum
2757328/11723>235 of the completed two-cycle arithmetic relaxation.
There are three new modules and six standard-axiom reports. These checks
do not discharge the inherited graph hypotheses or its complete Lean
potential certificate.

Next test the new critical012032 window with exact counts(3,5,4,5,3).
No match was found among135 saved actual snakes. Feasibility remains open.
See MATHEMATICAL_NOTE.md and handoff/NEXT_AGENT_PROMPT.md.

The paper was updated without definitions; source checks pass, PDF compiler
unavailable. The maintained interval remains191–235; goal ACTIVE.
""",encoding='utf-8')
summary="""# Research update: milestone139

The combined exclusion and uniform-credit graph calculation completed.
Means2446/5 and496 are attained by new five- and six-edge cycles with zero
credited events. Both credit83/3 comparisons remain above235. Independent
saved-result review passed. Lean checked the counted-suffix allowance24
and the resulting obstruction for every nonnegative uniform credit.
Even the completed two-cycle arithmetic relaxation has optimum
2757328/11723>235. This fixed credit route cannot supply the next integer
improvement; inherited local hypotheses and graph assembly remain pending.

Next: bounded feasibility test for012032 with exact counts(3,5,4,5,3).
None of135 saved snakes matches it. The maintained interval remains191–235.
Read milestones/139-exclusion-occurrence-credit/MATHEMATICAL_NOTE.md.
Paper update139 adds no definitions; source checks pass, PDF unavailable.
The separate115 batch was observed live at1056/1397. Goal ACTIVE.

"""
for n in ['README.md','COLLABORATION.md','RESEARCH_LEDGER.md','WORKSPACE.md','milestones/README.md','handoff/README.md','handoff/CURRENT_STATUS.md']:
 p=R/n;old=p.read_text(encoding='utf-8-sig');assert not old.startswith('# Research update: milestone139')
 p.write_text(summary+'## Earlier record\n\n'+old,encoding='utf-8')
prompt="""# Continue after milestone139

Work in E:/Snake-in-a-box, use the requested research skill, and define only
essential repeatedly used quantities. Preserve all three authors, the full
paper preamble/hypersetup and unrelated .gitignore/milestone50 changes.
Keep the existing D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex
editor and paper/snake9_research.tex synchronized. No new editor tab.
Fetch each round, preserve exact evidence, stage only a checkpoint manifest,
commit, push and verify. Goal ACTIVE; previous turn PROGRESS.

Read milestone139/MATHEMATICAL_NOTE.md, data/exclusion-credit83/results.json,
data/result-review.json and the three new Lean receipts. This round's
experiment finished; do not restart it. There is no live139 job.
The exact graph has4661772 edges after deleting only992157. Uniform credit
83/3 on8846 exact suffix events yields means2446/5 and496 with ranges2973/5
and602. Comparisons5520661/23446 and552097/2348 both exceed235.
All-edge potentials were checked by the evaluator; independent review checks
saved cycles/rows/potentials/arithmetic and does not repeat that entire scan.

Both new attaining cycles receive zero occurrence credit. Lean proves that
any nonnegative uniform credit, allowance and range cannot make the completed
comparison reach235 or the additional-share comparison reach234, given
their respective mean caps2446/5 and496. For allowance24 and the completed
four-/five-cycle caps, the arithmetic relaxation minimum is2757328/11723,
attained arithmetically atC12/5,mu2446/5,R0. No graph potential attaining this
range is claimed. Credit139 separately transfers the clipped event subset
to the actual24-window theorem. All3 modules/6reports passed standard axioms.

NEXT SELECTED ROUTE: ordinary local feasibility of012032 with EXACT five
counts(3,5,4,5,3). Relevant pair sum10; no endpoint theorem currently covers
it. Start a bounded necessary full-cube model, allow up to2 endpoints
without location or parity restrictions, and separate cycle-only SAT models
from actual paths. Reuse the pinned generic count and cycle encoders from138.
An UNSAT result needs a preserved certificate and actual-snake interpretation.
An actual SAT witness would refute ordinary exclusion and should guide a
subsequent endpoint or empty-square test. Do not assume its geometry.

The new completed5cycle edges are308566,3806548,2195856,163743,2303753.
Firstrowword012034054, sixcounts335453, suffix012032/fivecounts35453.
All135 saved actual snakes were revalidated;0 exact matches, despite136
suffix shape hits. See critical-witness-screen.json. The full-nine row is
a narrower fallback if the six-word condition is feasible.

The new additional-share6cycle edges are1274753,3051941,992121,1273780,
3047601,990202. Their exact rows are in the graph result. Do not conflate
profiles or treat count symbol6 as exact. The old138 cap(3,3,3,5,2) does
not match either new cycle and is not selected for an expensive Lean batch.

Inherited comparison assumptions remain: odd-length pair floor9, hypothetical
0123104 six-floor25, earlier unproved count sums, and extra share floors for
the additional profile. An even-length upper bound does not follow from
the odd-length comparison. Complete graph-to-snake/potential obligations
remain distinct. The maintained interval191–235 and unresolved196 persist.

Paper targeted update139, SHA recorded in paper-revision.json; no new
definitions, unchanged authors/preamble. Source checks pass; built-in
compiler failed before TeX. Last full revision136; next full146.

Milestone115 PID39044 was observed LIVE at1056/1397. Verify current process
command before acting; never duplicate it.104 stopped,122 and129 completed.
Lean gate>=1.5GiB free and at most2 existing Lean processes; fullgraph>=3GiB,
no concurrent fullgraph. Use exact source hashes and preserve all attempts.
Historical base commitd59f82f7d30c348d768c90edf56754c5bc877e39.
The new139 commit is identified by Git history/checkpoint manifest.
"""
(R/'handoff/NEXT_AGENT_PROMPT.md').write_text(prompt,encoding='utf-8')
print('Saved result, limitations, paper status and selected continuation.')
