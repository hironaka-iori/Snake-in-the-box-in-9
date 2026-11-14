# Revised main-paper review

Outcome: no unresolved blocking defect was found in the final reviewed revision. Three mechanical issues identified during review were repaired by the parent task and verified in the final source. The stronger actual-edge budget is justified under the stated premises. This is a source and argument review; no compiler, Lean process, solver, search worker, or software test was run. No manuscript was edited by this reviewer, and no new research was undertaken.

## Exact reviewed version

| Source | SHA-256 |
|---|---|
| Preserved `data/research-before.tex` | `4e902994337c8ef30d3d308e6915d7d43a80cb357570926fa23ab5fb42b8f73a` |
| Final `paper/snake9_research.tex` | `1774986363bdefddd5f05db5452b3b645da3f17602963d4fb8047b4489145594` |
| Final `scripts/rewrite_main.py` | `d822e30d6659f0bba3255b0fa002299dc9dc05153ec9385cb376cd698a6672fe` |

The final manuscript has 10,198 lines and 656,835 bytes. Its bytes match the open editor source at `D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex`. The author command and entire local `hypersetup` block are unchanged from the preserved original.

## Review performed

The complete textual change list was read. The large relocated construction block was compared separately with its original block so that its internal edits were visible rather than hidden by a large insertion/deletion. Relevant context was inspected around the short-count lemma, exact loss identity, boundary-24 proposition, actual-edge theorem, following potential corollary, historical five-window budget, and the positivity-guarded finite enumeration.

All 322 labels are preserved with the same multiplicities; there are no duplicate labels. Every textual `ref`, `eqref`, and `pageref` target resolves, and every cited bibliography key has an entry. These are source-level reference comparisons, without a compilation or rendered-layout claim.

## Strengthened actual-edge budget

The revised theorem at lines 2690–2733 retains the same local edge inequality and the same floor-profile assumptions. For a path with at least nine edges, the charged singleton positions are 8 through the penultimate position. The omitted positions are the two endpoints and the first seven internal vertices. The previously stated short-count lemma gives at least sixteen from those seven internals; the endpoints contribute at least eight. Therefore

\[
\sum_{r=0}^{m-9}\alpha_{r+8}+24\le T.
\]

Each physical share occurs in at most five windows. Summing the local inequalities consequently gives

\[
W+2880\le120T+5\Sigma=5G_{12}.
\]

The exact loss identity, with its zero-degree convention, gives

\[
5G_{12}+4200(m+1)+5L=1105680.
\]

Subtracting the endpoint/index contribution and the new boundary term yields

\[
W+4200m+5L\le1105680-4200-2880=1098600.
\]

No new count restriction, parity restriction, reference-catalogue premise, or positive-loss assumption is required for this total. The local floor choice remains a premise exactly where it was previously required. The reference-catalogue and potential hypotheses remain necessary for interpreting an actual path as a walk in the specified finite graph.

The following corollary intentionally retains the weaker historical constant 1098960 and its archived numerical substitutions. This remains valid: discard the nonnegative loss and weaken 1098600 to 1098960. The theorem expressly states that the boundary-21 totals follow as weaker consequences. Its revised written proof does not claim that a newly compiled combined theorem was produced in this review.

## Reorganization and scope

- The counting argument and construction argument now have separate parts. The numerical conjecture, whole-snake transformations, and coordinate-history restrictions were moved ahead of the final verification section. Their labels and mathematical statements are retained; historical experiments and witnesses remain in the appendices.
- The earlier reference to the optimality discussion was changed from “Appendix” to “Section”. References to the witness and construction-experiment appendices still point to material that remains there.
- The current retained graph and the older accepted-key package are now explicitly separated. Historical finite comparisons retain their original weights and boundary constants.
- The abstract and final verification paragraphs distinguish the archived contributor upper bound, the pending independent rebuild, native construction exclusions, and incomplete geometric/finite-certificate assembly. The new concluding construction paragraph states that 27 six-history cases remain unresolved; it makes no new bound or construction claim.
- The revised description of the undominated-corner argument correctly points to the stronger subsequent result. Its hypothesis is an undominated corner of a nontrivial snake; the new summary must continue to be read with that local context.

## Repaired findings

1. The initial revision inserted the positivity explanation after the unfinished phrase “shows that”, producing a malformed sentence before the displayed inequality. Final lines 8540–8542 place the explanation first and restore the complete lead-in.
2. The initial local-share replacement changed bare \(L\) to \(H\) while leaving \(L_i\) unchanged. The final historical five-window section consistently uses \(H_i\), including its definition, total, and overlap proof, and uses \(H\) for a generic local weight.
3. The nearby comparison-table paragraph still used bare \(L\) immediately after that symbol was defined as global loss. Final line 2783 explicitly uses \(H\) for the local share bound.

No unresolved accidental alteration was identified after these repairs. Compilation, page layout, and the final publication checkpoint remain the parent task's responsibilities. The requested pause after this round should occur after that wrap-up, without beginning another research round.
