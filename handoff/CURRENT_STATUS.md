# Current state after round 209

The goal remains ACTIVE. The user instructed continued work until she requests a stop. Round 209 is PROGRESS. No new Q9 witness, numerical bound or optimality proof was obtained; 196 remains unresolved. Read milestones/209-slice-capacity/MATHEMATICAL_NOTE.md and data/completion.json first.

The new geometric restriction is global over the fixed indexed histories. For two retained coordinates, equal free words in distinct intervals of the same parity are possible only for singleton visits at opposite square corners. Thus M + max(N0,N3) + max(N1,N2) <= 2^(r-1). The retained pair [0,5] has even counts M=12 and [N0,N1,N2,N3]=[5,4,10,10], saturating 32. Every even word occurs exactly once on the selected clique. Nine outside singleton intervals must share words with antipodal singleton partners. The individual partners are not prescribed. Opposite-parity constraints remain essential.

Three Lean modules pass with 13 dependency reports:
- Capacity209 checks finite capacity, saturation, unique carriers and partner support.
- Square209 checks square antipodes and singleton visit sets under cross-separation.
- ConcreteCapacity209 derives 81 intervals, even counts [12,5,4,10,10], odd counts [6,9,9,8,8], and the 32 selected indices directly from the literal 99-vertex source.
The complete actual-path/model assembly and native search certificates remain pending. Accepted sources, receipts and objects are immutable.

| Case | Retained coordinates | Committed jobs | Pending regions | Nodes | Status |
|---|---|---:|---:|---:|---|
| 24 | [0,4] | 150 | 8 | 9,625,900 | OPEN |
| 9 | [3,4] | 150 | 3 | 8,142,891 | OPEN |
| 23 | [0,5] | 100 | 7 | 2,683,356 | OPEN |

Cases 24 and 9 use the unchanged round 208 engine. Each inherits 100 steps and adds 50. Independent audit confirms all 1,200 inherited run files, checkpoint bytes and 100 new transitions. Case 23 uses a separately reviewed capacity engine with required-word support, unique-carrier forcing and partner-domain unions. Initialization validates the essential inequalities directly against the original binary tables. No general matching algorithm is implemented and no speed improvement has been established by a controlled comparison.

Only case 18, retaining [1,4], is excluded among the 28 six-coordinate models. All 56 five-coordinate models exhaust natively, so a different class requires at least SIX changed histories at the same length and index matching. No general seven-history conclusion follows. The other 24 unresolved pairs retain only their initial limited searches. Earlier geometric bridges from round 205 remain pending.

Round 210 is due for the whole-paper review; the previous review was round 200. Then continue the exact open frontiers. Freeze all round 209 evidence. In a new milestone, copy the unchanged original engine scripts, binary and input, plus the complete case-24 and case-9 directories. Also copy capacity_continue.py, capacity_solver.c, capacity_solver.exe, square-capacity.json, and the complete case-23 directory. Maintain their relative paths and exact engine/model pins. Use continue_search.py for cases 24/9 and capacity_continue.py for case 23, sequentially. Their roots follow their file locations. Do not regenerate pinned files or mix the two engines' states. A changed engine requires an explicitly justified frontier transfer.

All search sessions are terminal: 64506, 6803, 82960 and 56166. No native worker is active. Keep one heavy worker at a time. Search/Lean startup requires at least 1 GiB free, reserve at least 768 MiB, and process private bytes at most 256 MiB. Lean uses a 60-second limit with -j1 -s8192. The bounded 55-second startup wait retains these thresholds. No Python -O: the saved configuration records optimization 0, assertions enabled and no PYTHONOPTIMIZE. The continuation protocol assumes one coordinator. A manual per-job STOP marker does not promise whole-batch cancellation. Process recovery is supported; complete power-loss durability is unproved. No software tests were created or run.

The refreshed contributor branch is 7f549f144f5dae2ef9f6164757afd3f1e7bdbc25. Its 10:57 UTC report on 14 November records 3,124 / 3,127 modules built. The three remaining names are S012301A35344, T012304A33356K63 and T012304A35346K47. This is contributor-reported progress, without a merge or independent rebuild. The archived 235 rebuild is pending, and 233/234 remain conditional.

The editor originals in D:/Codex/2026-10-13/new-chat/outputs are mirrored byte for byte in E:/Snake-in-a-box/paper. Preserve authors and hypersetup. Compile the frontier first and main paper last, and consult the current receipts. The exact publication manifest limits scope. Preserve unrelated .gitignore, milestone 50 critical-family.json and pre-existing untracked files. Avoid unfiltered git status. There is no current pause request.
