# Current state after round 198

The goal remains active. Read milestones/198-symmetry-cliques/MATHEMATICAL_NOTE.md and data/completion.json. No new Q9 record or global numerical bound was obtained.

For row4147 of round197, the quotient is Q7 plus h, where h swaps(1,4),(3,6) and translates by126. The Q8 extension has minimum partner distance three. The quotient has eight disjoint K4s and32 triangles. Each clique contributes at most two path vertices. Coordinate0 is a product factor; its paired-clique crossing restriction is already implied by square cuts.

There are exactly three endpoint classes, of sizes32,64,32 with representatives10,2,0. They are distances0,1,2 from the triangle vertices. Paired translations, fixed-coordinate translations and pair exchange act transitively in each class. Thus three unrestricted fixed-endpoint cases cover every50-vertex quotient path. This reduction is invalid with an untransported fixed-seed constraint. The subgroup used also preserves ordinary Q7 edges, so the no-matching subfamily can use the same representatives.

Connected prefix regrowth gives a48-vertex quotient path using no matching steps and hence two47-edge Q8 paths. Their cross-distance histogram is[0,0,160,390,576,658,388,104,28], different from all 36 face forests saved in round195. This proves inequivalence to that comparison set, not to every face of every known Q9 snake. The witness is data/paired47.json. The first path starts63, ends1, and has transitions42104260210430240530421043024056042153124012310. The partner starts137 and ends255.

The18-vertex retained-prefix extension maxima are exactly46 and48 quotient vertices in the two orientations (447558 and31252 search nodes). The12-prefix searches stopped at35 seconds each; no upper conclusion follows. The connected circuit query for50 vertices and at most5 seed omissions is UNKNOWN90.047s. The new96-vertex paired face needs97 opposite-face vertices for192 edges; its four-port completion is UNKNOWN120.047s. All are restricted computations, not Lean contradiction certificates. Do not rerun unchanged timed-out models.

Accepted Lean modules: 89; theorem reports: 126. Endpoint transport checked: True. Complete concrete pair checked: True. Concrete triangle noncontainment checked: True. Pending sources: none. The generic endpoint reduction retains the full finite quotient and no seed premise. The exact three-orbit classification also has the written distance and transitivity argument.

An initial large endpoint-data proof exceeded256MiB; it was split into128-edge blocks. Startup refusals, interrupted compilation, failed source and plan snapshots are preserved. Use scripts/resume_proofs.py only for unfinished modules and scripts/check_core.py for an individual pinned check. Accepted artifacts remain immutable. All worker handles must be terminal before publication.

Next construction work: three unrestricted endpoint cases, or the simpler no-matching family S intersect h(S)=empty. Ordinary cube parity balance is valid only in the latter family. A50-vertex quotient path would give a100-vertex paired face, still requiring93 opposite vertices for192 edges or95 for194. Consider different near-optimal Q7 parent paths when a fixed parent stagnates; isometric copies of one parent are already covered by the symmetry placement census. Exhausting the three endpoint cases would restrict this symmetry, not establish a global Q9 upper bound.

Contributor branch 49636b49538b96ad8f437d8c6fc434d190de5b1f reports2998/3127 certificates built. Its diff and progress report are archived; it was neither merged nor independently rebuilt. Archived235 rebuild remains pending;233/234 remain conditional. Whole-manuscript review next at200.

Editor manuscripts remain D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex and snake9_frontier_explanation.tex, mirrored in E:/Snake-in-a-box/paper. Preserve authors, hypersetup and unrelated .gitignore and milestone50 edits. Keep one heavy worker,1GiB startup free memory,768MiB reserve,256MiB Lean process limit and60-second proof checks. Research remains active.
