"""Record the completed round without changing unrelated working files."""
from pathlib import Path
import json
H=Path(__file__).resolve().parents[1];R=H.parents[1]
summary='''# Research update: milestone 136

Four Lean modules and eleven theorem reports passed. The checked results
construct blocks of nearby window starts, bound the overlap of their covered
intervals, apply the run-length estimate to actual missing pairs, and count
the available outside coordinates. Maximal intervals in the full snake are
unnecessary for this block construction. No named definition is added.

The complete actual-snake occurrence bound remains sixteen per endpoint and
thirty-two in total under the checked common-neighbour assignment. Twelve
and twenty-four remain pending: the block construction must still be combined
with the boundary count, degree sums and exceptional case. See
`milestones/136-intervals-and-paper/MATHEMATICAL_NOTE.md` for the exact scope.

The paper is now revision 136. The existing editor source and repository copy
match, with all three authors and the complete hyperlink settings preserved.
The final source checks resolve every reference and reconstruct the two new
printed witnesses over 20,086 vertex pairs. The built-in compiler failed
before TeX execution because of a Windows helper restriction; the updated
PDF and its layout remain unverified. The next full paper revision is 146.

The recorded global interval remains 191–235, with incomplete independent
rebuilding of the contributor upper proof. Optimality and 196 are unresolved.
The fixed uniform-credit comparison still cannot lower the length bound
using an occurrence allowance of at least two. Further length improvement
requires its remaining cycle constraint or a stronger comparison.

The saved process observation found the milestone 115 job live at 917 of
1397 modules. Its incomplete progress is separate from this round's results.
Check the live process before any restart. The next selected task is the
actual-block assembly of the stronger endpoint count.
'''
for name in ['README.md','COLLABORATION.md','RESEARCH_LEDGER.md','WORKSPACE.md',
             'milestones/README.md','handoff/README.md','handoff/CURRENT_STATUS.md']:
    p=R/name;old=p.read_text(encoding='utf-8-sig')
    assert not old.startswith('# Research update: milestone 136')
    p.write_text(summary+'\n## Earlier record\n\n'+old,encoding='utf-8',newline='\n')
prompt='''# Continuation after milestone 136

Use E:/Snake-in-a-box and the requested research skill. Define only essential
quantities used repeatedly. Preserve authors Iori Hironaka, Tommy Ma and Steven
Zhan, all hyperlink settings, unrelated .gitignore and milestone 50 changes.
Check GitHub each round. Never restart an active certificate job or repeat
the large checked finite pair-capacity computation from milestone 134.

Read milestone 136/MATHEMATICAL_NOTE.md, audit/statement-review.md, verification
and checkpoint. Four modules and eleven theorem reports passed. The complete
actual-snake occurrence theorem remains milestone 135's total bound of 32
for fitting canonical 012032 starts with pair sum <=9, allowing overlaps and
both path parities. Its per-endpoint count of 16 uses an unselected common
neighbour; do not enlarge the assignment premise without a proved bridge.

Checked components now include:
- 132: the low-pair endpoint theorem and its complete certificate.
- 134: one normalization per endpoint, the unselected common neighbour,
  coordinate-pair representation, missing opposite pairs, injective actual
  coordinate sequences, and the actual run-length estimate.
- 135: even starts, label separation, actual union capacity, reversal and
  halving, endpoint partition and total 32; missing-degree identities.
- 136/IntervalBlocks136: constructs nonempty sorted blocks of starts by
  joining gaps <=2, with constant labels and gap >=3 between blocks; proves
  full interval coverage and the start-span estimate.
- 136/IntervalCount136: sums interval sizes with at most k-1 overlap and
  derives W+2k+1<=union cardinality under the explicit chosen bounds.
- 136/ActualMissingSets136: instantiates selected and absent pairs from an
  actual represented sequence starting at path index >=4; length is at most
  max(1,outside selected count)+t-degree.
- 136/OutsideCount136: outside selected count+crossing missing degree=8-a.

NEXT SELECTED TASK: finish the actual-block assembly for the stronger count.
Use the constructed blocks; maximal full-snake intervals are unnecessary.
Choose each block's first and last starts and constant common coordinate.
Prove every position in its expanded interval has the required common
neighbour. Remove sampled positions zero and one when present, and prove
these exceptional prefix positions occur in at most one block. Convert the
remaining consecutive positions into the actual coordinate sequence required
by ActualMissingSets136. Sum the bounds using MissingDegree135 and the actual
selected/missing pair capacity. Repeated labels are allowed; they only increase
the degree subtraction. Combine with OccurrenceArithmetic133.

For a<=7 the desired inequalities are
W<=7a-a(a-1)/2-t-2k+delta and W<=k(5-a+t)-t+1+delta.
The checked integer reduction under W>=12+delta leaves a=k=5,t=3.
OutsideCount136 gives the exact 3-crossing-degree count for this exception.
The degree identity and at-most-one three-crossing vertex are checked in 135.
Prove the resulting W+3k<=6a-4+delta and exclude a=8 separately. The complete
12-per-endpoint and 24-total results are pending. A total of 22 also requires
a checked boundary exclusion; the 133 native endpoint0 UNSAT is uncertified.

The old 13 theorem concerns both endpoints and has different hypotheses.
The 133 witnesses refute a uniform pair floor of 10, including with both
counts >=4. The fixed uniform-credit obstruction from 132 prevents a new
global length bound from an occurrence allowance >=2 alone. Keep the remaining
cycle constraint and stronger comparison requirement visible.

Paper revision 136 is saved in the existing editor path
D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex and the repository copy.
Both SHA256 hashes are
820820fafd255800cfe60f3c6cdde53dccc333ccaea2a49255299616458b1b0c.
Its preamble and authors are unchanged; no named definition was added.
The source and two new printed witnesses pass their checks. Built-in
compilation failed before TeX in the Windows helper. No rebuilt PDF or layout
check is claimed. Keep the existing editor open. Next full revision:146.

Recorded interval 191–235, with incomplete independent contributor-upper
rebuild; optimum and 196 open; goal ACTIVE. The saved observation found driver
PID39044 for milestone115 live at 917/1397. Verify its command before acting.
Milestone104 is stopped; 122 and 129 completed. Saved session IDs are historical.
Use the pinned runtime and checker resource gates; preserve every attempted
source and log. Stage only the exact next-round manifest, commit, push, and
verify the remote tip. Do not mark the research goal complete at a checkpoint.
'''
(R/'handoff/NEXT_AGENT_PROMPT.md').write_text(prompt,encoding='utf-8',newline='\n')
p=H/'data/paper-revision.json';q=json.loads(p.read_text())
q['status']='SAVED_SOURCE_CHECKED_COMPILER_UNAVAILABLE'
p.write_text(json.dumps(q,indent=2)+'\n',encoding='utf-8',newline='\n')
print('Updated seven status records and the continuation prompt; paper bytes unchanged.')
