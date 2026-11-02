# Independent review of the 012310 share closure

Reviewed 2 November 2026. The strongest checked mathematical result is a universal local share inequality for the six-direction shape 012310, with no prescribed singleton-count pattern. It does not establish a new global upper bound or the exact optimum.

## Mathematical statement and scope

Let p be any snake with m edges in Q9. Suppose a,b,c,d are four distinct coordinate directions in {0,...,8}, and six consecutive directions beginning at r are

\[
(a,b,c,d,b,a),\qquad r+6\le m.
\]

Then the five internal vertices of that window satisfy

\[
12\le\sum_{i=0}^{4}\operatorname{coreShare}_{12}(p,r+i+1).
\]

This is exactly `Snake9.LocalWindow.ShareWindow7305.share_bound` in `cases/case7305/lean/Share7305/Geometry.lean`. Its only hypotheses are the snake, the four distinct valid coordinate names, the six-step window bound, and the specified directions. It has no singleton-count premise, endpoint-position restriction beyond the window fitting, or local realization assumption supplied by the caller.

The proof derives the required five bounds 0 <= alpha <= 21 from the universal internal-vertex ceiling. All five vertices r+1,...,r+5 are strictly internal under r+6 <= m. The certificate cap is 11, so the integer contradiction gives lower bound 12 without an off-by-one change. The resolution is 12; the statement concerns the sum of the defined integer shares, not twelve empty square faces.

`Share7305/Reversal.lean` proves the same inequality for (a,b,d,c,b,a). Its reversed start is m-r-6 and the sum reverses precisely the five internal centres. Arbitrary relabelling is handled by the coordinate permutation. This reversed word has the same canonical shape after swapping c and d; no second distinct canonical shape is being claimed.

## Evidence independently checked

`cases/case7305/data/proof-audit.json` now has status `PASS_LOCAL_SHARE_THEOREM`, with 465 source modules and 100 printed theorem audits. All 465 present Lean source hashes were independently matched to the audit. For every module, a source-matched successful completion/semantic/composition record and compiled object were found. This read-only review did not start another compiler run.

The key checked chain was inspected directly:

1. `Share7305/Compose.lean` preserves the clause checks under concatenation.
2. `Share7305/Sat.lean` assembles all 86 semantic shards and derives satisfaction of the exact core CNF from the local axioms.
3. `LocalWindowUnsat/ShareWindow7305.lean` composes the replay segments and derives contradiction at the final empty clause.
4. `Share7305/Refuted.lean` applies `Tags.refutedShare_of_sat sat unsat`.
5. `Share7305/Geometry.lean` applies `refuted_share_bridge`, including arbitrary coordinate normalization and the derived count ceilings.
6. `Share7305/Reversal.lean` transfers the result to the reverse reading.

Their saved logs report only `propext`, `Classical.choice`, and `Quot.sound`, with the composition lemma using only `propext`. The local audit checks all printed audits, absence of placeholders, matching source dependencies, and the clause provenance. Imported local-window support is reused; this is not a fresh clean rebuild of that entire inherited closure.

The native CNF hash was independently compared with its certificate metadata. Its 83,898 clauses were read, the 11,008 selected original clauses were renamed through the recorded 5,360-variable map, and the result was compared with the saved compact CNF. The compact clauses were then compared with every flattened Lean raw-clause literal using the signed-literal encoding. Both comparisons passed.

The final source archive hash and the compressed CNF/LRAT hashes match `data/archive.json`. Decompressed compact certificate hashes and byte lengths also match that receipt. The LRAT record describes 154,489 derived clauses, 9,394,822 hints, 18,029 slots, 313 segments, and 78 checkpoints. The older pending archive and generation receipt are historical records; their pending wording does not override the completed proof audit.

## Combined catalogue

The refreshed `data/integration-audit.json` includes cases 7300, 7304, 7305, and 7306, with 35 printed theorem audits. Its generated-source hash matches the present `lean/CombinedCatalogue.lean`; the case7305 audit hash also matches. The saved combined log has no error or extra axiom marker, and its audit names include `Snake9.CatalogueIntegration73.canonical7305`.

The canonical wrapper states the share-12 result for either canonical orientation of shape 012310 in an arbitrary snake. The printed `partial_catalogue_share` signature was inspected. Its remaining local certificate premises are exactly:

| Case | Shape | Required lower share |
|---|---|---:|
| 7301 | 012032 | 16 |
| 7302 | 012034 | 20 |
| 7303 | 012301 | 16 |
| 7307 | 012340 | 16 |
| 7308 | 012345 | 16 |

There are five remaining local premises. The existing 012345 theorem supplies only 12, so it does not discharge case7308's target 16. Removal of the 7305 premise is justified by the newly completed theorem, without an additional count assumption.

## Exact finite-model comparison and its limit

The refreshed `data/proved-model.json` includes the exact case7305 proof-audit hash and has no `additional_share_assumptions`. It reports 1,601,856 states, 4,947,008 edges, exact mean 483, and integer potential range 551. Its weight and potential hashes exactly match the earlier assumed-012310x12 comparison. Thus the earlier comparison's local share assumption is now discharged; the numerical model itself is unchanged from that assumed calculation.

The saved attaining four-edge cycle was independently checked for closed endpoint incidence and mean (252+480+600+600)/4 = 483. The conditional boundary calculation was checked independently:

\[
(483+4200)m\le1098960+8\cdot483+551,
\qquad
m\le\frac{157625}{669}<236.
\]

This still gives integer bound 235 under the global graph/budget premises. The all-edge potential verification is recorded by the parent calculation; this bounded review inspected the verifier and saved receipt and checked the cycle, arithmetic, and local-source pins, without repeating the full graph computation. Its all-edge assertion is not a complete Lean replay of the graph potential.

No claim of 234 follows from this milestone. The full actual-snake graph interpretation, credit interpretation, potential replay, and the five remaining local share targets remain distinct obligations. The maintained global interval remains 191 through 235 edges. No construction longer than 191 or proof of optimality at 196 is established here.

## Review conclusion

No defect was found in the reviewed theorem hypotheses, normalization, five-centre indexing, reversal, cap-to-floor arithmetic, CNF mapping, or current catalogue signature. The completed local theorem and its canonical wrapper can be used without a prescribed count pattern. The report makes no novelty or sharpness claim.

## Receipt fingerprints

- `milestones/73-countfree-share-catalogue/cases/case7305/data/proof-audit.json`: `beb1c07d1a361fa4c4cfa037c504de38b93f06faa11275a7f16bf6743383a6ca`.
- `milestones/73-countfree-share-catalogue/cases/case7305/data/archive.json`: `f15e9e39053c8f1d10ac37e0661488a333097dff216284ee81ace794de51deab`.
- `milestones/73-countfree-share-catalogue/data/integration-audit.json`: `d90a4c77464c10db1d62a8b70cb7f14bb15fac5162ca01255128fd727d5d1d01`.
- `milestones/73-countfree-share-catalogue/data/proved-model.json`: `785956145396df7cf6230c446a9e7469b7c4b1713c6cf70d21a9091f1c8f7907`.
