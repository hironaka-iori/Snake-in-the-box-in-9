# Round 200 construction and explanation review

Reviewed on 13 November 2026. This is a source review with selective comparison against saved records. No manuscript was edited, no computation or proof replay was run, and no tests were created or run.

## Coverage

- Read every line 6303–8964 of `D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex`, from `sec:optimality` to the end, including construction and symmetry proofs, historical experiments, printed witnesses, the history-share catalogue and all bibliography entries. Long outputs were reread in smaller overlapping chunks where output truncation occurred.
- Read every line 1–961 of `D:/Codex/2026-10-13/new-chat/outputs/snake9_frontier_explanation.tex`.
- For the archived-bound wording, also read main-manuscript lines 129–144 and 327–380 and inspected targeted `rg` excerpts.
- At the end of this reading, the main source SHA256 was `d7a00426bb1e2349634563bf20966839af44d9b54c0e3bec2051d1c051495751`; explanation SHA256 was `223d5a708a62e89be513dce49995243e08d121df5910b189cd46e657b8b1d079`. Line numbers below refer to that source state.

## Required correction 1: failed merger searches are written as completed mergers

Location: main manuscript, `app:experiments`, subsection **Frozen components and larger cycle configurations**, line 7826.

The opening sentence says:

> Further mergers retained five or four of the 26-cycles and replaced the remaining selected vertices by one path of 66 or 92 edges.

This reports a construction that the underlying record explicitly says was not obtained. `milestones/15-component-mergers/README.md`, lines 3–4, states that no further component merger was obtained. Its table, lines 15–20, gives one restricted INFEASIBLE result and three UNKNOWN results. The saved inputs/results independently identify the target and status:

- `data/one-keep.json`: target 66 edges at line 140; INFEASIBLE at line 204.
- `data/one.json`: target 66 edges at line 140; UNKNOWN at line 204.
- `data/two-01.json`: target 92 edges at line 115; UNKNOWN at line 179.
- `data/two-02.json`: target 92 edges at line 115; UNKNOWN at line 179.

Proposed replacement for the first sentence:

> Further merger searches retained five or four of the 26-cycles and sought a replacement path of 66 or 92 edges.

The subsequent sentences about infeasibility, unresolved runs and the endpoint diagnostic can remain. This correction changes claim status, not a numerical value.

## Required correction 2: introduce the change of quotient in the explanation

Location: explanation lines 834–860, especially the first sentence after **Using symmetry to organize the next construction** at lines 854–856.

Lines 834–849 discuss the round-196 quotient of the first saved 47-edge pair. Its Q8 involution swaps coordinates 0 and 3, swaps 2 and 4, and translates by 63. The quotient is bipartite and has 16 forbidden double-lift pairs. After conjugation and deletion of a flipped coordinate, its Q7 representative involution has type `(2,1)`.

Lines 855–860 then refer to “the involution quotient from the preceding work” and assign it triangle vertices and three endpoint classes 10, 2 and 0. These properties belong to the different round-198 quotient, defined in main `sec:symmetry198`, lines 7543–7547. Its Q7 map swaps 1 with 4 and 3 with 6, then translates by 126. That map has type `(2,2)`; its Q8 extension has minimum displacement three, so it has no double-lift restrictions. The preceding bipartite quotient has no triangle vertices and cannot be the quotient described by the endpoint paragraph.

Proposed opening, before the existing endpoint-class claims:

> A different involution gives the quotient used in the current endpoint searches. In coordinates 0 through 6, let \(h\) swap 1 with 4 and 3 with 6, then translate by 126. Its graph consists of the ordinary \(Q_7\) edges together with \(x\leftrightarrow h(x)\). The corresponding \(Q_8\) involution has minimum displacement three and no double-lift restrictions. This quotient has three endpoint classes, represented by 10, 2 and 0.

The remaining sentences about distance from triangle vertices, symmetry and the three UNKNOWN searches are supported by the round-198 and round-199 records. No search status or numerical result needs alteration.

## Connection worth adding: contact pairs versus intersection vertices

Locations: main `sec:symmetry197`, lines 7507–7512; compare `sec:symmetry199`, lines 7674–7684 and 7715–7727.

The older census counts one unordered contact pair in each of two placements; the newer census counts at least two intersection vertices for every full-seed placement. These statements are consistent, but “contact” is not defined at the point of comparison. For a fixed-point-free involution \(h\), each unordered pair \(\{u,h(u)\}\) contained in \(S\) contributes two vertices to \(S\cap h(S)\). It also produces two cross-face edges in the direct two-face placement.

Add after line 7512, or at the transition to the general placement census:

> Here one contact counts one unordered pair \(\{u,h(u)\}\) of selected vertices. For these fixed-point-free maps, one contact means \(|S\cap h(S)|=2\), consistent with the minimum-intersection count in Section~\ref{sec:symmetry199}.

This is a missing connection, not an error in either census. It is especially relevant when interpreting a minimum-overlap placement as the starting point for coupled repairs.

## Optional precision: make the representative-change direction explicit

Location: main `sec:symmetry199`, lines 7686–7693.

The full-family conclusion is correct. The sentence “Replacing them by \(\alpha(S),\beta(T)\) changes the relative map to \(\alpha^{-1}f\beta\)” does not specify whether \(f\) is the map before or after normalization. If \(f\) is the original map, the transported map on the new representatives is \(\alpha f\beta^{-1}\). If \(f\) is a map on the new representatives, pulling back gives the printed \(\alpha^{-1}f\beta\).

An unambiguous replacement is the identity

\[
|\alpha(S)\cap f(\beta(T))|
=|S\cap(\alpha^{-1}f\beta)(T)|.
\]

Then state that the maps on the right still range over every cube isometry. This matches the intended argument. The saved `IsometricPlacement199.lean` proof transports an original map forward as \(\alpha f\beta^{-1}\); it supports the same equivalence. I found no resulting mathematical error in the full-family exclusion.

## Optional claim-status consistency in historical paragraphs

The main introduction and `thm:main` expressly preserve the independent-rebuild qualification for the archived upper bound 235. The following later standalone passages use less qualified language:

- Main line 8101: “the current interval \(191\le a(9)\le235\)”.
- Main line 8114: “the upper bound 235 in Theorem~\ref{thm:upper235}”.
- Main line 8273: “The later six-centre proof ... establishes the current interval”.
- Main bibliography `bound235archive`, line 8627: the source title “Completed six-centre bound of 235: proof assembly and dependency audit”.

These are not independent contradictions because the qualification is stated in the referenced theorem. Nevertheless, line 8273 is easy to read as a claim of a completed local rebuild. Prefer “The later archived contributor six-centre argument ... supplies the project interval ..., with the complete independent rebuild still pending.” At lines 8101 and 8114, adding “archived” is sufficient. Preserve the actual bibliography title; an annotation after it may repeat the rebuild boundary if desired.

The explanation's opening and closing correctly retain conditional status for 233/234 and the independent-rebuild qualification for 235. Round-200 reporting should update its date, final record range and manuscript-review statement only after the current round's work is complete. The existing review sentence at lines 952–955 still describes the round-190 review, and should then refer to the completed round-200 review without suggesting a proof rebuild occurred.

## Findings that did not require correction

- The exact two-layer and three-component joining conditions account for all cross-face edges and use edge/vertex counts consistently.
- The component, colour, retained-vertex and moving-endpoint accounting identities have valid written deductions under their stated path assumptions.
- The four-crossing forest criterion includes connectivity, avoiding the path-plus-cycle ambiguity.
- The involution classification and the written clique/orbit arguments are consistent with their stated coordinate maps.
- The arbitrary-isometry criterion \(S\cap f(T)=\varnothing\), allowance for distinct parent shapes, and absence of an automatic involution quotient are correct.
- The 199 placement table agrees with `data/completion.json`: one published self-pair, six unordered 50-plus-50 cases including self-pairs, and fourteen 51-plus-49 cases; 645120 maps per completed pair; minima 2 except two mixed cases at 3.
- The 100-vertex face completion counts 93, 95 and 97 for Q9 targets 192, 194 and 196 are consistent with total length \(|A|+|B|-1\).
- No new Q9 witness is claimed in the current construction summary. The repeated-move cutoff of 33 edges is kept separate from the single-replacement-plus-extension cutoff of 44.

## Sources consulted beyond the assigned manuscript text

Read in full:

- `E:/Snake-in-a-box/handoff/CURRENT_STATUS.md` (round 199).
- `E:/Snake-in-a-box/milestones/199-parent-diversity/MATHEMATICAL_NOTE.md`.
- `E:/Snake-in-a-box/milestones/199-parent-diversity/data/completion.json`.
- `E:/Snake-in-a-box/milestones/199-parent-diversity/lean/IsometricPlacement199.lean`.
- `E:/Snake-in-a-box/milestones/198-symmetry-cliques/MATHEMATICAL_NOTE.md`.
- `E:/Snake-in-a-box/milestones/197-symmetry-placement/MATHEMATICAL_NOTE.md`.
- `E:/Snake-in-a-box/milestones/196-quotient-cycle-cuts/MATHEMATICAL_NOTE.md`.
- `E:/Snake-in-a-box/milestones/15-component-mergers/README.md`.

Read selectively:

- First 110 lines of `milestones/198-symmetry-cliques/data/completion.json`; not treated as a complete receipt audit.
- Opening lines and target/status fields of the four milestone-15 JSON files listed under correction 1.
- Discovery search excerpts in milestone Markdown records and `milestones/197-symmetry-placement/scripts`; only identified records were used as evidence for findings.
- Memory registry `C:/Users/hironakaiori/.codex/memories/MEMORY.md`, lines 60–90, supplied the older round-182 orientation and warning about verification boundaries. Current round-199 status was then read directly. No memory was changed.

## Limits

This review did not rerun witness pair checks, enumeration programs, solver inputs, Lean modules, the archive rebuild, compilation, rendering or external bibliography retrieval. Printed transition strings and certificate tables were read but were not independently recomputed. Existing verification claims are not upgraded by this review. The two required corrections concern a source-supported result-status error and an unintroduced change of mathematical object. The other proposed edits improve precise interpretation and do not imply new proof failures or new bounds.
