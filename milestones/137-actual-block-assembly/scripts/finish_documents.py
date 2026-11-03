"""Save the completed occurrence theorem and focused continuation."""
from pathlib import Path
import json
H=Path(__file__).resolve().parents[1];R=H.parents[1]
summary='''# Research update: milestone 137

The complete actual-snake bound of twenty-four low-pair windows passed Lean.
Any finite set of fitting canonical 012032 starts with relevant pair sum at
most nine has size at most 24, allowing overlap and either length parity.
The checked per-endpoint count is 12 under the unselected-common-neighbour
assignment. Nine modules and 23 theorem reports passed; the final source
also received an independent mathematical and scope review.

The proof constructs actual blocks, counts the exceptional prefix once,
subtracts actual missing pairs from capacity, sums degrees with repeated
labels allowed, and excludes both exceptional parameter cases. The previous
total 32 is improved to 24. The boundary-free count eleven, arbitrary distance-only assignment,
sharpness and a new global length bound remain unresolved.

The paper received a targeted update 137 with the completed proof. No named
definition was added. Its authors and complete preamble are unchanged, and
both saved copies match. Source checks pass; the built-in compiler failed
before TeX in its Windows helper. The updated PDF and layout are unverified.
Last full revision 136; next full revision 146.

The maintained interval is 191–235, with incomplete independent rebuilding of
the contributor upper proof. The optimum and 196 remain open. The uniform
credit obstruction persists even with an allowance of two events. Next:
investigate a necessary endpoint condition on the other seven-edge cycle,
which has no 012032 event. Read milestones131–132 and the new137 note before
setting a bounded local counterexample query. Retain all model assumptions.

At the saved process observation, the separate milestone115 certificate job
was live at 952/1397 modules. Check its command before any restart. The current
checkpoint is progress toward the active research goal, not completion.
'''
for name in ['README.md','COLLABORATION.md','RESEARCH_LEDGER.md','WORKSPACE.md',
             'milestones/README.md','handoff/README.md','handoff/CURRENT_STATUS.md']:
 p=R/name;old=p.read_text(encoding='utf-8-sig')
 assert not old.startswith('# Research update: milestone 137')
 p.write_text(summary+'\n## Earlier record\n\n'+old,encoding='utf-8',newline='\n')
prompt='''# Continuation after milestone 137

Work in E:/Snake-in-a-box. Use the requested research skill. Define only
essential repeatedly used quantities. Preserve authors Iori Hironaka, Tommy
Ma and Steven Zhan, the complete hyperlink settings, unrelated .gitignore
and milestone50 changes. Fetch each round, preserve exact evidence, stage
only the checkpoint manifest, commit, push and verify the remote tip.

COMPLETED: the actual twelve-per-endpoint and twenty-four-total occurrence
theorems now passed Lean. Read milestone137/MATHEMATICAL_NOTE.md and
audit/statement-review.md, then the exact receipts and checkpoint. The final
source is lean/ActualCount137.lean, SHA256
6c663ff371f792efe9078f34b3a1bca87334c8e1f5716ef4653e4c544b11eaaf.
Its final check took 53.156s and printed four reports with standard axioms only.
All nine137 modules passed; there are 23 reports altogether.

The final low_pair_count_le_twenty_four theorem applies to any finite set
of distinct fitting canonical 012032 starts with coreAlpha(r+2)+coreAlpha(r+4)
<= 9. Overlap and both path parities are allowed. The assigned_count_le_twelve
premise is the common unselected neighbour supplied by CommonNeighbor134.
Do not enlarge it to arbitrary Hamming-distance-only assignments. The proposed
boundary-free count eleven and total 22 remain unchecked, and no sharpness is asserted.

The completed137 chain includes actual interval-to-coordinate-list construction,
ordered block bounds, exact prefix counting, capacity with actual missing
pairs removed, degree sums permitting repeated labels, the exceptional
a=k=5,t=3 bound, the a=8 exclusion, and endpoint normalization/partition.
Do not repeat the completed assembly or the costly PairCapacity134 computation.

NEXT SELECTED TASK: investigate the OTHER seven-edge cycle for a necessary
endpoint condition. Continue the endpoint route, now addressing the cycle
that avoids012032 and hence survives the count24 restriction. First read
milestones/132-odd-pair-endpoint/audit/credit-limitation.md and its data/
credit-limitation.json, and milestones/131-odd-pair-six-count/data/
odd-pair9-six25/results.json. Reconstruct the exact direction/count windows
and distinguish suffix events from overlapping prefix placements. Compare
the cycle with the proved catalogue and saved actual-snake witnesses before
selecting the cheapest local query. Test candidate endpoint consequences
with a bounded counterexample search. A native UNSAT result requires its
semantic interpretation and checked certificate before it becomes a theorem.

The four-edge cycle's first-profile weights are 480,496,360,616, mean 488;
only two suffix events per period are counted. The other seven-edge cycle
has first-profile weights 732,376,366,376,616,251,736, mean3453/7, and zero
012032 events. Its mean under the additional-share profile is 496. Do not
conflate profiles. The fixed uniform-credit arithmetic is already checked:
even an event allowance of 2 cannot make that comparison reach 235 or below.
An allowance 24 alone cannot lower the global bound. Conditional graph floors
and the graph-to-snake proof obligations remain explicit. Assess new local
results with both the proved catalogue and stronger conditional premises.

The paper has a targeted update 137, preserving full revision 136's structure.
Editor D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex and repository
paper/snake9_research.tex have SHA256
8d98ae0a58e9e1748fe73bc78ca1786ee05415490a4cef7f6087228f24d885ad.
No named definition was added. The new proof was read independently and
source structure/reference checks pass. Its unchanged witness appendix reuses
the pinned136 verification. Built-in compilation failed before TeX in the
Windows helper. No rebuilt PDF/layout verification is claimed. Keep the
existing editor open; next full paper revision 146.

The recorded interval remains 191–235, with incomplete independent rebuilding
of the contributor upper proof. The optimum and 196 remain open; goal ACTIVE.
The previous turn is PROGRESS. Snapshot137 found milestone115 PID39044 live
at 952/1397. Verify its actual command before acting. Milestone104 is stopped;
122 and129 completed. Never duplicate a live job. Respect the checker resource
gate, including free memory and existing Lean processes. Preserve all attempts,
exact dependencies and source bytes. Full-graph jobs need the stronger memory
gate. The historical base commit is120eb35cff441474aca79c4e38e2fb96e2ec9785;
the new137 commit is identified by Git history and the file manifest.
'''
(R/'handoff/NEXT_AGENT_PROMPT.md').write_text(prompt,encoding='utf-8',newline='\n')
p=H/'data/paper-revision.json';j=json.loads(p.read_text())
j['status']='SAVED_SOURCE_CHECKED_COMPILER_UNAVAILABLE'
p.write_text(json.dumps(j,indent=2)+'\n',encoding='utf-8')
print('Saved current status and exact continuation; paper bytes unchanged.')
