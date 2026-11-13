# Current state after round 199

Research remains active. Read milestones/199-parent-diversity/MATHEMATICAL_NOTE.md and data/completion.json. No new Q9 witness or global bound was obtained.

Symmetry has two roles. The round198 involution quotient still has three endpoint classes10,2,0. Its unrestricted50-vertex cases all remain UNKNOWN after45 seconds each, with no seed constraint. The earlier checked96-vertex paired face remains available in milestones/198-symmetry-cliques/data/paired47.json; its192-edge completion was unresolved.

For two Q7 paths with sets S,T, placing S in one Q8 face and f(T) in the other gives separated components exactly when S intersect f(T) is empty. f may be any cube isometry; no involution and no equality of parent shapes is required. This broader placement statement does not give an involution quotient. Five Lean statements in IsometricPlacement199 pass, covering path images, layer embedding, separation, representative changes and reversing pairs. Numerical censuses remain native, with no Lean replay.

Every completed relative-placement scan covers all5040 coordinate permutations and128 translations, hence645120 maps per pair. The published51-vertex parent's self-pair has minimum intersection2. All six unordered pairs from the three saved50-vertex parent classes have minimum2. Of14 published51-plus-saved49 cases,12 have minimum2 and2 have minimum3. Thus none produces the desired100-vertex paired face. Independent canonicalization of distinct parents is valid for the full isometry family, generally invalid for an involution-only scan.

The three50-vertex and fourteen49-vertex parent banks exhaust extensions of the two24-vertex prefixes of the published seed. They do not classify all Q7 paths. Two16-prefix attempts stopped at3000001 nodes each and added no new class. Save and reuse the complete placement results rather than scanning isometric copies again.

A circuit query for any49-vertex induced path in the complement of the published51-vertex parent remains UNKNOWN60 seconds. The complement has77 vertices and141 edges. This permits arbitrary second-parent shapes and has no symmetry or seed-overlap restriction. A witness would give100 paired-face vertices, still needing93 opposite-face vertices for192 edges,95 for194 or97 for196. A pair alone does not establish a Q9 lower bound.

Next: use minimum-overlap placement geometry for coupled repairs, or derive stronger complement-path restrictions before rerunning an unchanged timed-out model. Matching-step quotient paths remain another route. Whole-manuscript review is due in round200.

Contributor branch 0cb8450707e481db49b6204587e45db9ae0df589 added4 replay-generation log entries. The diff is archived; no independent rebuild or merge was done. Archived235 rebuild remains pending;233/234 remain conditional.

Editor manuscripts are D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex and snake9_frontier_explanation.tex, mirrored in E:/Snake-in-a-box/paper. Preserve authors and hypersetup, plus unrelated .gitignore and milestone50 modifications. Keep one heavy worker,1GiB startup memory,768MiB reserve,256MiB per Lean process and60-second Lean checks. Research is active.
