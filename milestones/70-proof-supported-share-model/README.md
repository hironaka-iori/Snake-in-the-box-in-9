# Milestone 70: proof-supported comparison and recovered restrictions

**Completed research round on the unconditional proof track.** A complete comparison model now uses only local rules supported by recorded Lean proofs. Forty additional proved restrictions from milestones 47–50 have been recovered and integrated. They remove the displayed three-transition obstruction, but another cycle retains exact minimum normalized mean four. The global bound remains 235; this round establishes no new unconditional bound.

The current conditional target remains 234 with the explicitly selected additional count premises of milestone 69. Work alternates between improving that target and strengthening the proof-supported model.

## Reference model without numerical-only premises

The builder reads the union of the contributor's completed 235 and 236 count catalogues, giving 1,378 distinct reference keys. It uses the four checked forward share inequalities and their reversals, the checked nine-direction forced-absence geometry, and the checked eleven-direction improvements and count restrictions integrated in milestone 67. Numerical-only count catalogues and share screens are not read by the builder.

Applying the reference count keys at every represented subwindow gives 6,086,947 transitions. Its exact integer minimum is 480, normalized to four, with potential range 600. A three-transition cycle repeats truncated counts 1,5,6. Symbol six denotes an actual count between six and 21.

Two additional count keys occur on that cycle. Cross-checking the proof inventory shows that one was already implied by the milestone-49 theorem for directions

\[
(a,b,c,a,d,e),
\]

which excludes simultaneous first and fourth internal counts at most two. In particular, the count pattern (1,A,5,1,B), with A,B between six and 21, is impossible. A new Lean wrapper checks this application to arbitrary coordinate names and arbitrary snakes. No new SAT refutation is needed for this consequence.

## Recover proved restrictions across the model

The integrated family contains:

- Three single-count exclusions from milestone 47.
- Two pair-sum restrictions and one asymmetric pair exclusion from milestone 48.
- Thirty-three pair exclusions from milestone 49.
- The triple-sum lower bound 13 from milestone 50, used as an exclusion only when all three recorded counts are below six.

These forty rules are applied in both orientations wherever all counted positions are represented. Count-six symbols are never treated as exact values in an upper-sum contradiction. The excess demanded above six by the triple theorem is not yet used as an additional charge here.

The rules exclude 1,089,429 more transitions, leaving 4,997,518. They remove the original three-transition cycle. The replacement has four transitions with entering counts 4,3,5,4 and weights 480,360,600,480. Its average integer weight remains 480. The potential range falls to 578.

Thus the exact finite-model comparison is:

| Model | Transitions | Exact integer mean | Potential range |
|---|---:|---:|---:|
| Reference count catalogues and checked shares | 6,086,947 | 480 | 600 |
| Above plus forty recovered proved rules | 4,997,518 | 480 | 578 |

The replacement cycle consists entirely of exact count symbols below six. Its persistence therefore cannot be attributed to the ambiguity of the six-or-more bucket. It is a cycle in the finite relaxation, not a constructed snake.

## Boundary consequence and limitation

With the strengthened boundary budget, the enriched model supplies the conditional inequalities

\[
W+4200m\le1098960,
\qquad
480(m-8)\le W+578.
\]

Consequently

\[
4680m\le1103378,
\qquad
m\le\frac{551689}{2340}<236.
\]

The integer consequence is 235. Even replacing the potential range by zero cannot make slope 480 exclude m=235 under this boundary budget. Lean checks this limitation as well as the arithmetic deduction. A stronger slope, stronger boundary accounting, or a different argument is required for 234.

## Verification and scope

- `data/verification.json` independently reconstructs all 6,086,947 baseline transitions, their weights, the potential inequalities and attaining cycle.
- `data/enriched-verification.json` performs the corresponding complete check on all 4,997,518 enriched transitions.
- `data/lean-audit.json` records five theorem audits: the arbitrary-snake application of the existing pair restriction, the conditional bound arithmetic, the slope limitation and the replacement-cycle weight sum.
- `data/import-audit.json` checks current source hashes against the saved verification receipts for milestones 47–50. Imported proof closures are reused, not rebuilt.
- `data/critical-missing-keys.json` preserves the initial numerical-catalogue comparison. Its key 297 is subsequently discharged by the existing milestone-49 pair theorem; the filename does not assert that every listed key remains unproved.

All local rules in this comparison have recorded proof support. The complete arbitrary-snake normalization/history assembly and full Lean graph-potential replay are still missing. The numerical graph check must not be presented as a new completed global proof.

## Next round and reproduction

The next conditional round should use the recovered rules to reduce the count-dependency selection and examine stronger empty-square charge on the replacement critical configurations. The corresponding proof round should certify useful new inequalities and continue the arbitrary-snake assembly. Conditional targets and unconditional bounds remain separate entries in the research record.

Run `build.py`, `analyze.py`, and `verify.py` for the baseline. Add `--enriched` to each command for the forty-rule model. Run `audit_imports.py`, `replay.py --resume`, and `audit_lean.py` for the proof records. Large generated graph arrays and compiled objects are ignored. Source data, compressed potentials and verification receipts are retained.

This is round 4 of 10 after manuscript revision 66. The paper and open editor mirror remain unchanged. The next full rewrite is scheduled for milestone 76.
