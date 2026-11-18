# Chat transfer after Round 240

Prepared on 19 November 2026, Asia/Tokyo. This is a handoff, not a new research round. The old chat's goal remains paused. The next chat should use GOAL_PROMPT.md as the goal text.

## Files to read

1. `GOAL_PROMPT.md` in this folder: the objective and working rules.
2. `STATE.json` in this folder: source hashes, Git revisions, saved proof scopes, and live checks made during this handoff.
3. `../../milestones/240-five-count-recovery/MATHEMATICAL_NOTE.md`: complete five-count argument.
4. `../../milestones/240-five-count-recovery/STRUCTURAL_NOTE.md`: the symmetry reduction, explicit eight-point limitation, bounded classification, and star family.
5. `../../milestones/240-five-count-recovery/data/completion.json`: accepted evidence and inherited frozen searches.
6. `../../further-research/2026-11-19-post-round-240/RESEARCH_DIRECTIONS.md`: proposals and deductions to investigate next, separated from the completed checkpoint.

All paths above are relative to this folder. The repository is E:/Snake-in-a-box. The goal prompt and further-thoughts folder are intentionally separate.

## Verified checkpoint and scope

Round 240 was published at `cdc9efe96c837f28b9c0d6b305320218444e8b5b`. At handoff, local HEAD and fetched origin/main still matched this research checkpoint. The original goal tool reported paused. Creating these transfer files does not resume it.

| Result | Evidence and remaining gap |
| --- | --- |
| Recovery from 509 of 512 counts | Complete actual-cube Lean theorem from Round 238. |
| Recovery from 508 counts | Written cube proof, two native geometric enumerations, and 87 Lean matrix implications from Round 239. Complete cube assembly remains open. |
| Recovery from 507 counts | Written cube proof, 372 Lean matrix implications, 6,435 column descriptions, 90,396 arithmetic cases, and independent enumeration of 2,699,004 vertex triples from Round 240. Complete cube assembly remains open. |
| Known-parity recovery from 251 of 256 counts | Written consequence of the five-count result. |
| Recovery with eight missing counts and no missing distance-eight pair | Written cube argument with supporting generic Lean arithmetic from Round 239. |
| Smallest nonzero count-change support between six and nine | Written consequence of five-count recovery and the one-vertex example. Values six, seven, and eight remain unresolved. |
| Explicit eight-point matrix solution of amplitude 21 | Lean-checked literal witness; it violates the necessary actual count bound nine. |
| Only zero survives the actual count bound in that eight-point configuration | Written Walsh-character proof, independently reviewed, without its full Lean assembly. |
| Entire-support distance-eight stars of at most eight points are excluded | Written proof. It cannot be applied independently to a star coupled to another component. |

The last reviewed snake-length interval is 191 <= a(9) <= 231. The completed contributor theorem and saved audit are pinned to `478869ee1ec6ff3a10ddb6ba7a2a1d89fbb82088`; its entire dependency chain has not been independently rebuilt here. The current handoff refreshes main and research/unconditional-241, whose reviewed checkpoint remains `d32557fb4eec570dd69267ffc23768517541f9ae`. Its Track B report explicitly claims no new bound. Other remote branch heads are inventoried in STATE.json; their contents have not all been reviewed in this handoff. Do not infer theorem status from a branch name.

No new snake witness, global upper bound, Lean proof, or finite mathematical search was produced during this handoff.

## Construction work to preserve

The saved-seed comparison excludes overlap above 186 for a hypothetical 192-edge snake under the recorded finite/native family covers. Such a candidate must omit at least six vertices of every saved 191-edge seed and add at least seven. The saved bank is not an exhaustive list of all possible 191-edge snakes.

At exactly four minority replacements, class 139 is natively excluded; classes 7, 6, and 0 remain UNKNOWN; 141 classes are unqueried. A timeout is not an exclusion. The next majority exchange family removes two old vertices and inserts three. The full frozen-state paths and hashes are in the Round 240 completion record.

For the saved 98-edge parent and its isometry class, the recorded one-crossing family cannot improve 191. The specified two-block family is excluded through width 46 for all crossing counts. These are construction-family results. Different parents, block lengths, and less restricted joins remain possible. Re-read the relevant sections of the paper before changing a search restriction.

## Documents and environment

Authoritative sources:

- D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex
- D:/Codex/2026-10-13/new-chat/outputs/snake9_frontier_explanation.tex

Their exact repository mirrors are in E:/Snake-in-a-box/paper. The last successful compiler receipts are in milestone 240. This handoff reads and hashes them; it does not recompile unchanged documents. Full written-source review occurred at 240, with the next due at 250.

Preserve all three authors and the exact local hypersetup. Keep the existing editor tab when editing. Lean 4.19.0 was used for this round; execution plans under milestone 240 retain the exact runtime path, source pins, compiler arguments, and resource limits. Discover available runtime paths in the new environment before running anything.

Two unrelated tracked edits were present at handoff: `.gitignore` and `milestones/50-three-count-return/excess-screen/data/critical-family.json`. Preserve them and any newer changes. Avoid recursively enumerating every untracked file in this large repository. Use scoped paths and bounded output.

The final checkpoint's publication manifest records status before the pause tool was called; the actual goal was subsequently paused after the successful push. The historical phrase "pause requested after publication" in that manifest is not an instruction to repeat publication or resume work.
