"""Record the checked scope and the unresolved proof requirement."""
from pathlib import Path
import json
H=Path(__file__).resolve().parents[1];R=H.parents[1]
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
records=[read(p) for p in (H/'logs').glob('*/record.json')]
passed={Path(q.get('importable_object','')).stem:q for q in records if q['status']=='PASS'}
assert {'ActualSplit129','ActualCounters129','ActualTriple129','CoreSemantics129'}<=set(passed)
assert sum(len(passed[m]['axioms']) for m in ['ActualSplit129','ActualCounters129','ActualTriple129','CoreSemantics129'])==17
assert read(H/'data/export-review.json')['status']=='PASS_EXPORTED_BYTES_SEMANTICS_AND_PACKED_PROOF'
update=r'''# Research update: milestone 129

The fourth-count-three case of the 0120324 window now has a complete native
contradiction, independently replayed through all 50082 deductions. Its
3500 selected clauses use fewer hypotheses than the original search, supporting
the candidate implication

$$
\alpha_{r+4}=3\quad\Longrightarrow\quad
\alpha_{r+3}+\alpha_{r+5}+\alpha_{r+6}\ge12.
$$

Lean checks the exhaustive case split, the actual-snake count conversions,
and satisfaction of all 3500 clauses under the contrary hypotheses. It also
checks the triple lower bound and the equality-case six-count lower bound 23
conditional on the contradiction of this exact input. These four modules
have 17 successful axiom reports. The complete 221-module Lean refutation is
still running. The candidate implication therefore remains unproved without
that remaining premise. See milestone 129's mathematical note and verification
record for the exact saved progress.

The earlier endpoint batch has also completed. An independent audit verifies
all 448 modules and 30 axiom reports. For a fitting canonical 012032 window,
equality of the second and fourth counts' sum to eight forces both centres
to have Hamming distance two from both endpoints. There are at most thirteen
such starts in any snake. The final theorem has no remaining local-certificate
premise. This occurrence bound needs a further global argument before it
can improve the upper bound on snake length.

The complementary fourth-count-at-least-four case remains unresolved. No
universal six-count bound or improved global upper bound is claimed. The
maintained interval remains 191–235, with the documented independent-rebuild
limitation on the contributor upper-bound proof. The optimum and 196 remain
open. No new mathematical definition is introduced. Paper revision 126 is
unchanged; the next scheduled full revision is 136.

'''
# Keep the previous dated record available; this update states the current scope.
for name in ['README.md','COLLABORATION.md','RESEARCH_LEDGER.md','WORKSPACE.md','milestones/README.md','handoff/README.md','handoff/CURRENT_STATUS.md']:
 p=R/name;old=p.read_text(encoding='utf-8-sig');assert not old.startswith('# Research update: milestone 129')
 p.write_text(update+'## Earlier record\n\n'+old,encoding='utf-8',newline='\n')
readme=update.replace('# Research update: milestone 129','# Milestone 129: the fourth count equal to three',1)
readme+='''## Saved evidence

- MATHEMATICAL_NOTE.md gives the argument using the existing notation.
- audit/branch-input-review.md checks the new input and full native proof.
- audit/transport-review.md checks every reduction and input mapping.
- audit/export-review.md independently checks all selected clauses, meanings,
  packed deductions, checkpoints, slot reuse and exported source changes.
- audit/core-semantics-derivation.md records the checked actual-snake meaning.
- audit/endpoint122-completion-review.md records the completed endpoint theorem.
- archives/endpoint122-completion-*.tar.gz preserves all 1528 newly completed
  endpoint evidence files that were absent from the repository index.
- data/proof-plan.json pins the 221 exported Lean modules.
- data/replay-progress.json is the live local progress; the frozen observation
  in audit/observed-replay129.json records the checkpoint's exact prefix.
- data/verification.json and data/file-manifest.json identify the saved bytes.
- archives/ preserves the native traces and original generated sources as
  separately verified lossless gzip files; the raw local files are retained.

Run scripts/verify_saved.py --restore-archives after a fresh checkout, then
scripts/verify_saved.py --verify. Inspect the process and replay.lock before
resuming scripts/run_replay.py --timeout 600. Never start a duplicate worker
or remove a live lock.
The driver reuses verified receipts and waits for sufficient resources.

The first replay attempt encountered a Lean import-root lookup error before
checking Data0. A verified byte-identical copy of the CNF object into the
replay build directory fixed it. The failed attempt is retained. The original
generated sources use CRLF; the ported sources use LF, with the exact change
independently checked and recorded. No unrecorded source normalization was made.
'''
(H/'README.md').write_text(readme,encoding='utf-8',newline='\n')
prompt=r'''# Continuation after milestone 129

Work in E:/Snake-in-a-box and use the requested research skill. Use ordinary
notation; introduce a definition only when essential and repeatedly used.
Preserve the three authors, local hyperlink settings, unrelated .gitignore
and milestone 50 edits, and active proof jobs. Refresh GitHub first, with
automatic Git maintenance disabled for the fetch to avoid duplicating the
repository's ongoing maintenance.

Read129/MATHEMATICAL_NOTE.md, the three independent audit reports, the actual
semantic derivation, and data/checkpoint.json. Restore archived raw traces
with scripts/verify_saved.py --restore-archives when needed on a fresh checkout.

The candidate is: in a fitting canonical 0120324 window, fourth count 3 forces
the sum of counts3,5,6 to be at least 12. The selected contradiction uses no
six-total or pair premise. Counter 0 encodes at most two endpoints; counter 4
the fourth lower bound 3; counter 11 its upper bound 3; counter 12 the contrary
triple upper bound 11. The 63 corner occurrences must retain multiplicity
over 57 distinct vertices. All 512 primary and 512 endpoint meanings are retained,
including semantic inputs that never occur as packed proof literals.

CoreSemantics129 now proves actual satisfaction of all 3500 selected clauses
under fourth=3 and triple<=11. Its actual_triple_lower and actual_six_lower
still have the explicit Unsat premise. Four helper/semantic modules have 17
successful reports with standard axioms. Do not report the actual exclusion
until the complete refutation and final assembly succeed.

The root replay driver is scripts/run_replay.py --timeout 600. Inspect
data/replay-progress.json, replay.lock and current process commands before
resuming. The frozen checkpoint is a prefix of 221 modules, not a completed
proof. Reuse exact receipt/source/object/log/dependency hashes. Its fixed
checker is LratFast with 13-bit keys and offset 2400. All 1695 proof variables
fit; the actual maximum used key is 8190. There are 435 segments and 108
checkpoints. Do not confuse the number 6902 of distinct keys with their maximum.

After the full Lean contradiction passes, add the small actual-snake assembly
using the checked concrete semantics. Check the final theorem's axioms and
state the exact result. Only then report the equality case excluded. The
next mathematical case is fourth>=4 under six-total<=22. The first>=3 and
second>=5 deductions are specific to fourth=3 and cannot be assumed there.

Milestone 122's endpoint driver reported completion during this round. Its
independent completion review is saved alongside 129 if present. Read the
audited theorem assumptions before using its at-most-13 equality-window count.
It is a separate completed theorem, not a global upper-bound improvement.
The 104 and 115 drivers remain separate pending proof obligations; inspect
their current processes and progress rather than restarting them.

The maintained interval is 191–235, with the contributor upper-proof rebuild
limitation. A single-pattern six-floor 23 does not prove 234. Continue the
empty-square/global shortfall route once the local proof is closed. Paper 126
is unchanged, with full revision next due 136. Preserve the open D: editor
source and E: paper mirror; do not claim successful PDF compilation from the
last restricted-token failure. Keep all hypotheses and numerical observations
separate from completed theorems.
'''
(R/'handoff/NEXT_AGENT_PROMPT.md').write_text(prompt,encoding='utf-8',newline='\n')
print('Wrote current research scope and continuation instructions.')
