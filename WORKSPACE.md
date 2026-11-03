# Active research workspace

The authoritative directory is `E:\Snake-in-a-box`. Run research and Git commands from this directory.

The maintained manuscript is `paper/snake9_research.tex`. Its authors are Iori Hironaka, Tommy Ma, and Steven Zhan. The existing editor mirror is `D:\Codex\2026-10-13\new-chat\outputs\snake9_research.tex`. Check both files before synchronizing; preserve independent user edits. Keep the editor tab open, preserve the local hyperlink settings, and use the built-in compiler after manuscript changes. Keep Lean source identifiers and build details out of the mathematical paper.

## Current direction

Current checkpoint: [milestone 126](milestones/126-paper-revision/README.md).
The selected route uses six consecutive singleton counts and retains empty
squares. The maintained range is 191–235 with the documented upper-proof
rebuild limitation; universal local floors and sufficient shortfall bounds
remain unresolved. The manuscript revision through 125 is saved in both
source locations, with no new definitions and preserved authors/settings.
The built-in PDF compiler failed before TeX; source verification passed.
The next full paper revision is 136.

Next task: implement the reviewed cardinality-clause proposal saved in
milestone125/data/next-encoding-task.json, using its actual repository path
`milestones/125-critical-six-count/data/next-encoding-task.json`.
Inspect existing live proof drivers before restarting anything.

## Historical checkpoint notes



The latest theorem is [milestone 41](milestones/41-joint-intervening-sum/README.md). For directions (a,b,c,d,e,c,a,d), first and seventh internal singleton counts at most three imply that the third and sixth counts sum to at least 12. Ten Lean audits passed, including a generic counter identity, the 5,222,602-hint replay, exact geometric interpretation, and overlap accounting. If the corresponding truncated counts sum to at most 11, each occurrence forces one excess unit; multiplicity two gives 12 charge units per occurrence. No occurrence-frequency lower bound is known. All 131 bank paths were checked: 1,442 direction-pattern occurrences, none meeting the two low-count caps. The global interval remains 191 <= a(9) <= 236.

The preceding local result is [milestone 40](milestones/40-intervening-counts/README.md). For directions (a,b,c,d,e,c,a,d), if the first and seventh internal singleton counts are both at most three, then the third and sixth counts are each at least five. Eight Lean audits passed, including both refutations and arbitrary coordinate normalization. These restrictions eliminate the saved 119/29 diagnostic cycle at its identified occurrence. Twenty-three independent local forest checks establish local attainments and controls; no new global bound or minimum cycle mean is claimed. The strongest manuscript interval remains 191 <= a(9) <= 236.

The current manuscript interval is **191 <= a(9) <= 236**. [Milestone 39](milestones/39-audited-bound-236/README.md) incorporates the completed radius-four theorem from contributor commit `7cb52aad`, with all 732 window refutations and a successful saved Linux dependency audit. The paper now supplies its full potential, boundary, endpoint, and incidence argument. An independent local enumeration checks 1,026,432 candidate transitions, and four new Lean arithmetic checks passed. The complete contributor proof has not been independently rebuilt here; selected proof interfaces and audit receipts are pinned separately from the earlier local proof build.

The preceding research checkpoint is [milestone 38](milestones/38-four-position-obstruction/README.md): 17 Lean audits prove asymmetric distance-four singleton restrictions. For directions (a,b,c,d,e,c,a,d), the first and seventh internal counts X,Y satisfy X >= 2, X <= 2 implies Y >= 4, and Y <= 1 implies X >= 9. Consequently X+Y >= 5, 2X+Y >= 8, and X+6Y >= 15. A qualifying distant singleton forces three units of count excess above the truncated value six. Seventeen local forests have independent checks, including boundary pairs (2,4), (3,2), and (9,1); full-snake sharpness remains unresolved. The saved diagnostic cycles survive these restrictions, and the integrated interval at that checkpoint was 191 <= a(9) <= 238.

The manuscript revision is recorded in [milestone 37](milestones/37-logical-paper-rewrite/README.md), dated 24 October. The main text now follows the complete square-identity, finite-window, potential-sum, and endpoint argument for 238. All 175 exclusions are printed; five Lean arithmetic audits and an independent check of 1,026,432 candidate transitions passed. Detailed classifications and search records are retained in appendices. The existing editor source is synchronized, with authors and hyperlink settings preserved. Compilation was blocked at that checkpoint; the current manuscript compiled successfully during milestone 40.

The preceding mixed-count checkpoint is [milestone 36](milestones/36-critical-cycle-consistency/README.md): two seven-centre mixed-count exclusions have passed six Lean audits, including arbitrary coordinate labels. They eliminate the previously saved critical cycles. The diagnostic witness-table mean rises from 1739/360 to 29/6; a replacement lower-table cycle remains at 119/29. The integrated interval at that checkpoint was 191 <= a(9) <= 238. Milestone35 retains the proved three-square share bonus and its occurrence accounting.

A foundational local theorem checkpoint is [milestone 33](milestones/33-distance-three-singletons/README.md), dated 23 October. Nine Lean audits establish distance-three singleton-sum bounds 10 and 9 for direction patterns `(a,b,c,d,e,b,a)` and `(a,b,c,d,e,b,f)`, respectively, with all named coordinates distinct. A disjoint six-cycle argument explains both bounds. There are no conditions on the intervening counts. The 131-path bank supplies 956 checked occurrences. The pair inequalities raise the recorded witness-table cycle mean from 287/60 to 1739/360; the lower-table mean stays 119/29. These diagnostic means do not establish a global bound.

[Milestone 32](milestones/32-seven-count-four-screen/README.md) has 18 Lean audits covering arbitrary-snake normalization, the 34-case classification, a conditional frequency consequence, and four completed geometric refutations. The remaining 30 numerical cases still need replay or deduction from other theorems; six consecutive singleton counts equal to four remain conjecturally excluded. All 34 native certificates have been generated, with pending exports kept as local intermediates. [Milestone 31](milestones/31-joint-counter-soundness/README.md) retains its completed weighted joint-excess bounds. The integrated interval at that checkpoint was 191 <= a(9) <= 238.

Milestone33 replays and wrappers are complete; its build location is in milestone33/build/latest.txt. Milestone32 has completed cases 0,1,14,22 and all conditional bridges in build/proofs-latest.txt. Other native exports are available locally but their Lean replays are pending. The current paper compiled successfully with the desktop editor compiler during milestone 40. Milestone32 short five-centre indices0,1,6 and independent six-centre23 are UNKNOWN; do not claim those are exclusions.

Construction work through milestone25 is committed. Uncommitted milestone26 preserves a 186-edge interior-change witness checked in Lean and six growth runs returning186, without improvement. Do not delete it or confuse it with milestone27. Disable automatic maintenance on Git commits to avoid a long repack after the commit is created.

## Verification and synchronization

Distinguish Lean-checked theorems, ordinary finite computation, solver UNKNOWN, restricted solver exclusions, and conjectures. A completed research checkpoint does not complete the overall goal. Each milestone has its own scripts, data and proof receipts; maintained TeX remains under paper/.

Fetch GitHub before each round. Inspect collaborators' new work without replacing local manuscript settings or unrelated edits. Stage intended files explicitly, validate saved hashes against the index, push the checkpoint, and verify the remote head. Preserve the existing unrelated .gitignore change, contributor files and untracked PDFs/logs.

Use `git -c safe.directory=E:/Snake-in-a-box` where required. Lean 4.19 and pinned mathlib reside under `D:\Codex\2026-10-01\it-should-have-a-property-of\work\lean-research`. Run Lake from the mathlib directory with the dependency paths documented in the milestone logs and scripts. Running Lake from this repository alone does not configure mathlib.

The built-in LaTeX preview has recently failed before compilation with a Windows split-writable-root sandbox error. Attempt compilation after source updates and record the actual result; do not present old PDFs as current successful builds. Historical transfers, experiments and proof work remain in the research ledger, milestone folders and Git history.
