# Round 195 complete; goal active

The user explicitly resumed after the round 194 pause and requested construction methods based on 6-to-7 and 7-to-8. Read milestones/195-shortened-reroutings/MATHEMATICAL_NOTE.md and data/completion.json.

Current focus: four-crossing lifts made from two Q8 paths in one face and three in the other. Two 49-edge paths give 100 face vertices; a compatible95-vertex opposite forest would give 194 edges. This is a target, with no construction or optimality result yet.

The observed Q8 two 25-edge components are exchanged by swapping coordinates 2/5 and XOR73. The involution extends to Q8 and has partner distances3 or 5. Its 128-vertex quotient gives a route to symmetric nonadjacent path pairs. Lean checks generic lifting and separation, the finite involution and neighbour properties, and a safe-step version for distance-two involutions. Eleven accepted modules have 16 theorem reports.

The restricted1536-isometry, two-subpath, one-crossing construction has native maximum42 edges, giving86 face vertices. The saved Q9 bank has balanced 47-edge paired components under different involutions;20 labelled maps were found. The first such map has distance-two partners. Keep the full quotient adjacency and forbid selecting both endpoints of double-lift edges. Do not simply delete those edges.

Next: use scripts/affine_search.py and the first observed 47-edge pair, replacing connectivity flow with an induced-degree relaxation and sound cycle exclusions. The initial target is 50 quotient vertices, hence two 49-edge paths. Its at-most-four-omission bound counts quotient orbits, equivalently at most8 omitted vertices from the 96-vertex paired forest. It does not bound each labelled component separately. Widen that restricted neighbourhood if excluded. A valid paired forest still needs the opposite-face completion; scripts/four_crossings.py gives the precise four-port model including singleton outer components and connectivity.

Current UNKNOWN runs: quotient50(120s); affine50-omit4(90s); lower-four 98(30s); bank-four 192(120s). No exclusion follows. Fixing both face selections reconstructs known 98- and 191-edge paths; all-pairs verification passes. The earlier short-state scan stopped for low free memory after 6 completed states and 238 discovered states, so its closure is incomplete. Its source is preserved and the sampling-interval bug was corrected afterwards. Do not repeat an unchanged timeout.

Inherited round 194 result: one block replacement through 44 edges then endpoint addition excluded for 131 saved 191-edge Q9 snakes; repeated-move closure only through 33. Known suboptimal48-edge Q7 comparison has minimum block in[38,43]. No new Q9 record or global upper bound in 195.

Archived 235 still awaits a complete independent rebuild;233/234 remain conditional. Round 187 has 93/98 batches and 11904/12424 clauses; critical contradiction and actual-snake transfer pending. The contributor branch remains ecc47830c77df280f402f851799336dc81a7f680 at the opening refresh; its reported2659/3118 production modules were not independently rebuilt. Whole-manuscript review next at 200.

Keep the existing D:/Codex/2026-10-13/new-chat/outputs manuscripts authoritative and mirror E:/Snake-in-a-box/paper. Preserve author order and hypersetup. Preserve unrelated .gitignore and milestone50 critical-family edits. Keep one heavy worker,1GiB startup free memory,768MiB reserve,256MiB Lean limit,60s proof checks, and bounded solver runs. All research processes must be terminal before publication.

Final contributor refresh: branch advanced to dfa35ffd592587f62125cf7b4871cbd9e04c3c0f, adding ten production/replay data lines in two files. The diff is saved in milestone195 data/contributor-final.diff; it was neither merged nor independently rebuilt.
