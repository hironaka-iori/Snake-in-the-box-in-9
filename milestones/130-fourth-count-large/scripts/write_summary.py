"""Publish the checked local results without adding mathematical definitions."""
from pathlib import Path
import json
H=Path(__file__).resolve().parents[1];R=H.parents[1]
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
assert read(H/'data/independent-actual-final-audit.json')['status']=='PASS'
assert read(H/'data/independent-odd-pair-audit.json')['status']=='PASS'
assert read(H/'data/replay129-completion-archives.json')['complete_refutation_at_snapshot']
assert read(H/'data/equality-completion-review.json')['status'].startswith('PASS')
update=r'''# Research update: milestone 130

Two local inequalities are now proved for actual snakes. For a fitting
canonical direction window 012032 beginning at position r,

$$
\alpha_{r+2}+\alpha_{r+4}=8
\quad\Longrightarrow\quad m\equiv r\equiv0\pmod2.
$$

Consequently the pair sum is at least nine whenever the snake length or the
window start is odd. The proof uses the completed endpoint theorem and the
ordinary parity of cube vertices. No new mathematical definition is introduced.

For a fitting canonical window 0120324, Lean also checks

$$
\alpha_{r+4}=3\quad\Longrightarrow\quad
\alpha_{r+3}+\alpha_{r+5}+\alpha_{r+6}\ge12.
$$

Together with the established first and second count bounds, this gives a
six-count sum of at least 23 in that case. All 221 modules of the exact
contradiction and the final actual-snake application passed. The final
statements have no remaining local-certificate premise. The complementary
case with fourth count at least four remains unresolved: its separate search
timed out without a model or contradiction. Lean checks the meaning of all
717 added clauses for that case, which does not exclude it.

The parity restriction removes the saved four-edge witness for odd-length
snakes. The saved eighteen-edge witness has no matching pair window and
survives. Its most frequent seven-direction shape is 0123104. A proposed
six-count floor 25 for that shape increases this witness's hypothetical mean
from 2915/6 to 3011/6, but the full graph has not been recomputed. The next
selected test is that full comparison, preserving every inherited unproved
hypothesis and combining overlapping credits by their maximum.

The maintained interval remains 191–235, with the documented incomplete
independent rebuild of the contributor upper-bound proof. No improved global
bound is claimed. The optimum and 196 remain open. Paper revision 126 is
unchanged; the next scheduled full revision is 136.

'''
for name in ['README.md','COLLABORATION.md','RESEARCH_LEDGER.md','WORKSPACE.md',
             'milestones/README.md','handoff/README.md','handoff/CURRENT_STATUS.md']:
 p=R/name;old=p.read_text(encoding='utf-8-sig')
 assert not old.startswith('# Research update: milestone 130')
 p.write_text(update+'## Earlier record\n\n'+old,encoding='utf-8',newline='\n')
readme=update.replace('# Research update: milestone 130','# Milestone 130: parity and the fourth-count equality case',1)
readme+='''## Evidence and continuation

- MATHEMATICAL_NOTE.md gives the deductions and their exact scope.
- audit/odd-pair-derivation.md explains the parity result; the module has
  eight checked reports and its rebuilt dependency has four.
- audit/equality-completion-review.md audits the full 221-module refutation
  and the three final actual-snake statements.
- audit/large-review.md and audit/large-derivation.md distinguish the
  complementary search timeout from its checked 717-clause interpretation.
- audit/odd-cycle-review.md checks the two saved cycles only.
- data/next-pressure-task.json records the selected full-graph experiment.
- data/replay129-archives.json and data/replay129-completion-archives.json
  preserve the new proof evidence beyond the previous checkpoint. The first
  records a 199-module intermediate snapshot; the second completes all 221.
- data/trace-archives.json preserves the two incomplete native traces.
- data/batch-observation.json records the other proof jobs at checkpoint time.
- data/checkpoint.json, data/verification.json and data/file-manifest.json
  give the precise saved status and file hashes.

After a fresh checkout, run this milestone's scripts/verify_saved.py
--restore-archives and then --verify. It restores prerequisite archives from
milestone 129 as well as this milestone's archives. Existing evidence
is never overwritten by archive restoration. Inspect the live milestone 115
process and lock before any restart. Milestone 104 stopped after its own
timeouts and has not been resumed. Milestone 129's refutation is complete.

The first native attempt in this milestone was interrupted without a terminal
record. The separate resumed attempt timed out after 300.172 seconds, using
29.546875 seconds of process CPU time. Both incomplete traces are retained
locally and in verified lossless archives. Neither establishes an exclusion.
'''
(H/'README.md').write_text(readme,encoding='utf-8',newline='\n')
note=H/'MATHEMATICAL_NOTE.md';s=note.read_text()
begin='<!-- BEGIN EQUALITY STATUS -->';end='<!-- END EQUALITY STATUS -->'
before,tail=s.split(begin);_,after=tail.split(end)
status=r'''
The full 221-module contradiction replay and the final application to actual
snakes have now passed Lean. For every fitting canonical 0120324 window,

$$
\alpha_{r+4}=3\quad\Longrightarrow\quad
\alpha_{r+3}+\alpha_{r+5}+\alpha_{r+6}\ge12.
$$

The existing first-count lower bound three and second-count lower bound five
then give

$$
\sum_{j=1}^{6}\alpha_{r+j}\ge 3+5+3+12=23.
$$

Thus any such window with six-count total at most 22 must have fourth count
at least four. The final three checked statements have no remaining
local-certificate premise. This closes the equality case only.
'''
note.write_text(before+begin+status+end+after,encoding='utf-8',newline='\n')
prompt='''# Continuation after milestone 130

Work in E:/Snake-in-a-box and use the requested research skill. Keep existing
notation; add a definition only when essential and repeatedly used. Preserve
the three authors, hyperlink settings, unrelated .gitignore and milestone50
changes, and active proof jobs. Fetch GitHub with automatic maintenance disabled.

Read milestones/130-fourth-count-large/MATHEMATICAL_NOTE.md, its independent
equality-completion and odd-pair audits, and data/checkpoint.json. This
milestone's restore command includes prerequisite129 archives. The archived
199-module prefix is followed by a separate complete221-module record; do
not mistake the earlier snapshot for the final status.

Completed actual-snake results:
1. Fitting canonical012032, pair8 forces even length and even start. Thus
   pair>=9 if either is odd, including every fitting window of length235.
2. Fitting canonical0120324, fourth=3 forces triple(3,5,6)>=12 and six>=23.
   A total<=22 therefore forces fourth>=4. The full contradiction and final
   application passed; no unproved local Unsat premise remains.

The complementary fourth>=4 input has105246 clauses. Its717 new clauses have
checked actual meaning, but the full conjunction and complete contradiction
remain unresolved. The300-second retry timed out. Prefix replay5000 is not
a full proof. Do not import the equality-case first>=3 or second>=5 here.

NEXT SELECTED TASK: evaluate both full finite-graph profiles with the proved
odd-length pair floor9 and the proposed0123104 six-count floor25. See
data/next-pressure-task.json. The18-edge saved witness contains this shape
ten times. Its hypothetical mean becomes3011/6; that is not a new graph
minimum. The native0123104 probe in124 is UNSAT_UNCERTIFIED. Retain all
inherited unproved sum hypotheses. Only pursue its expensive certificate
if the full graph improves. Preserve clipped symbol6 as[6,21], the exact
first-symbol guard, and maximum combination of overlapping credits.

Use121/scripts/evaluate_pair.py and124/scripts/evaluate_six_shapes.py as
references. Record source hashes, all-edge inequalities, attaining cycles,
potential ranges and conditional comparisons. Gate a full graph run on
at least3GiB free memory. Do not duplicate live Lean jobs. Milestone115 is
still pending;104 stopped after timeouts;129 is complete. Inspect current
progress and process commands rather than inferring liveness from old files.

The maintained interval remains191–235 with the contributor-proof rebuild
limitation. No local result alone proves234 or233. The optimum and196 are
open. The goal remains active. Paper126 is unchanged; full revision next136.
Keep the D: editor source and E: paper mirror. Last PDF compilation was
blocked before TeX by the split-root Windows token issue; do not claim a
successful PDF. Preserve every interrupted or failed attempt and exact
audited bytes. Commit/push a verified checkpoint at the end of each round.
'''
(R/'handoff/NEXT_AGENT_PROMPT.md').write_text(prompt,encoding='utf-8',newline='\n')
print('Wrote milestone130 results and continuation.')
