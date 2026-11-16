# Round 233 final document review

**No outstanding blocking issue found after the abstract correction recorded below.** The universal parity-projection criterion, isolation-cover argument, restricted ceilings, and verification limits are consistent with the audited sources and finite evidence. No improved Q9 witness or new global upper bound is claimed; the maintained interval remains 191 <= a(9) <= 233.

## Reviewed scope

Read the complete new `sec:parity233`, the changed date and abstract, the new verification paragraph and bibliography entry, the short section “Why the simple dimensional lift fails” with its adjoining transition and remaining questions, and all 41 lines of `MATHEMATICAL_NOTE.md`. Read both new Lean modules and their accepted audit receipts and compiler logs. This is a bounded review of the round-233 additions and their immediate dependencies, not a fresh complete review of the 12,408-line main manuscript.

## Mathematical assessment

The projection criterion is valid in both directions. The selected lift of x is (x,c(x)), where c is binary-weight parity. An opposite-parity vertex over y is adjacent to this lift exactly when x equals y or is a base neighbour of y. Thus its complete selected-neighbour set is the closed-neighbourhood intersection used in the contraction. A Hamiltonian ordering gives an induced lift: each inserted label has exactly its two intended neighbours, distinct ordering edges cannot reuse the same physical label, and each lifted colour class is independent.

Conversely, a snake of 2k-2 edges has k vertices in its endpoint colour class. Flipping the last coordinate when necessary makes that class even. The last bit of an even vertex is determined by the parity of its first n bits, so projection is injective and recovers a k-element base set. The intervening odd vertices give precisely the labelled Hamiltonian edges. The main proposition explicitly assumes k >= 2. The argument does not require the base set to be an induced path; that restriction is introduced only in the subsequent finite construction family. The text correctly states that the parity lift itself is not a cube isometry and that the universal criterion retains the original existence difficulty.

The isolation lemma is sound. If an initially isolated retained vertex x lies farther than distance two from every deleted vertex, no selected neighbour of any label that could meet x is removed. Its selected-neighbour set cannot newly become a two-element set incident to x. Therefore every initial isolated vertex must either be deleted or be within distance two of a deletion. The covering-incidence inequality allows overlaps and supplies a necessary condition only.

The numerical deductions agree with the saved finite audit:

| Saved parent | Necessary deletions | Reason | Lifted edge ceiling |
|---|---:|---|---:|
| Q6 parent, 26 edges | 3 | Any two deletions cover at most 9 of 10 initially isolated vertices. | 46 |
| Q7 parent, 50 edges | 4 | 37 initial isolated vertices; one deletion covers at most 12. | 92 |
| Q8 parent, 98 edges | 5 | 69 initial isolated vertices; one deletion covers at most 17. | 186 |

These ceilings concern every successful deletion-only majority parity lift of the particular saved parent, using edge length 2m-2r. They do not assert attainability or bound arbitrary snakes in Q7, Q8, or Q9. A singleton retained set gives a trivial zero-edge path and causes no exception to the stated ceilings. The stronger arbitrary-deletion conclusions follow from the covering argument; they are not misrepresented as additional exhaustive Hamiltonian searches.

The vertical-crossing explanation is also valid under its induced-base-path hypothesis. A retained label already has its own vertical neighbour and is eligible exactly when it has one retained base neighbour. These labels are the two ends of each nonsingleton retained path component. Deleting r vertices leaves at most r+1 components. Each used retained label contributes one vertical edge; labels outside the retained set contribute none. Consequently the lift has at most 2(r+1) vertical crossings. The document correctly leaves component counting and its whole-path interpretation as written arguments.

## Finite and checked evidence

All quoted finite counts match `lift-audit.json`: 6,763 cases, 6,698 isolated-vertex exclusions, 27 excess-leaf exclusions, two disconnected graphs, eight native infeasibility results, and 28 verified witnesses. The witnesses all lie in Q6: two have 24 edges and 26 have 22. All 6,657 cases from the saved parents in dimensions 6, 7, and 8 are excluded by directly verified isolated vertices. The eight solver-dependent cases concern the Q5 parent. The documents preserve the distinction between the four saved parents and an exhaustive classification of all parent paths.

The four `ParityLift233` statements cover opposite-label adjacency, lift injectivity/disjointness, independence of the two lifted classes, and the retained-label neighbour characterization. Their hypotheses require a proper Boolean colouring where used. The two `IsolationDeletion233` statements transfer a locally unchanged selected-neighbour witness and preserve isolation under local retention. The isolation statement includes distinct endpoints in the two-neighbour witness. These are appropriately general supporting results; they do not themselves establish the whole-cube projection theorem, the radius-two interpretation, the finite coverage maxima, or the incidence/component counts.

Both saved receipts have status `PASS`, exit code zero, and no stop reason. Current source, object, and compiler-log hashes agree with the receipts. The four parity-lift reports use only `propext`; the two local-deletion reports use no axioms. This review did not invoke Lean or rebuild inherited dependencies.

| Evidence | SHA-256 |
|---|---|
| `data/ParityLift233-audit.json` | `e929badfe1248f26daf81c8555e50059632fbbd1ffd04c6938f14c96beec6caa` |
| `lean/ParityLift233.lean` | `18cb138c282c4b10b2b5992994ad08f9c2a21758edb0b44eec5ea7fb85f74e30` |
| `data/IsolationDeletion233-audit.json` | `2e4fc64552e20e0cadfbb68c23021f4a464559b62c8a7f6d378d51e80e5e08be` |
| `lean/IsolationDeletion233.lean` | `18cb588ea1185c62f3901e169cb09c9c9d39d31bb9be758cec9b4f9908b7921f` |

These paths are relative to `milestones/233-parity-lift-construction`. The documents accurately distinguish the six accepted statements from the remaining written bridges, direct finite verification, and eight unreplayed native contradictions.

## Correction verified and remaining scope

The first abstract said the deletion obstruction excluded near-doubling from “each saved lower-dimensional parent”. That included the saved 13-edge Q5 parent, for which two successful one-deletion lifts have 24 edges. The final abstract now explicitly restricts the obstruction claim to the saved parents of lengths 26, 50, and 98. The corrected wording was reread in the authoritative original and matching mirror. No further revision is requested by this review.

The proposed one-exchange minority-class family remains explicitly unsearched. The text retains the completed contributor 233 bound and its independent-rebuild qualification, and identifies round 233 as the pause point. Neither the universal reformulation nor the restricted deletion ceilings are used to claim a new global bound.

## Preserved settings and final document hashes

The complete author commands and complete `hypersetup` command match the round-233 pre-edit snapshots. Iori Hironaka, Tommy Ma, and Steven Zhan retain their order and existing formatting. The main PDF metadata/settings are unchanged; the short paper still has no separate `hypersetup` command. Each original is byte-identical to its corresponding `E:/Snake-in-a-box/paper/` mirror.

| Final file | Bytes | SHA-256 |
|---|---:|---|
| `D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex` | 776123 | `b7d4060eff1a496ae20f914cb073e628e92a5cdf26d71b6e3f8c73597af2eec7` |
| `D:/Codex/2026-10-13/new-chat/outputs/snake9_frontier_explanation.tex` | 41257 | `9180c81346644701946fff1b7bfc3c7afa11fdef0dc61e076b885b0cc2ed6d59` |
| `E:/Snake-in-a-box/milestones/233-parity-lift-construction/MATHEMATICAL_NOTE.md` | 5783 | `584a6a1af10c86355b15fdc9ff4cac9bc294002367bca6dbe68b94ab2adee5c0` |

The main and short documents contain 12,408 and 770 lines, respectively. Only this report was written. No compiler, solver, software test, or document edit was performed. LaTeX compilation and rendered-page inspection remain separate from this source review.
