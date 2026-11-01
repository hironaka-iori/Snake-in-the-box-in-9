# Critical-family empty-square investigation

This investigation belongs to milestone 72, which remains in progress. The global interval remains $191\le a(9)\le235$.

## Exact finite-model obstruction

The frozen six-case checkpoint at commit `dba1a62a` has minimum integer mean 480. All its minimum-charge cycles lie in six strongly connected components containing 6,125 states and 18,865 transitions. These transitions represent 498 canonical five-centre windows, and all have zero recorded share credit. The component sizes in states/transitions are 3,398/10,543; 2,611/8,144; 2/2; 106/168; 4/4; and 4/4.

`verify.py` checks every recorded component in both directions and proves that contraction of those components leaves an acyclic tight-edge graph. It also checks every source edge, window label, and potential inequality. This independently establishes completeness of the finite critical-family extraction. The full arbitrary-snake interpretation of the model remains pending.

The snapshot predates the two latest count proofs. Its source hashes and six applied cases are retained explicitly. `candidate_effect.py` separately uses the current eight-case model; the two graphs must not be conflated.

## Share inequality, now checked in Lean

Let six consecutive transitions use six distinct coordinate directions, and let $x_1,\ldots,x_5$ be the internal vertices. Suppose their singleton counts satisfy

\[
(\alpha_1,\alpha_2,\alpha_3,\alpha_4)=(4,5,4,2),\qquad 6\le\alpha_5\le21.
\]

With the established integer-share notation, the proved local inequality is

\[
\sum_{i=1}^{5}\sigma_{12}(x_i)\ge120.
\]

The radius-four local model has a verified acyclic witness with counts $(4,5,4,2,11)$ and individual shares $(28,31,21,11,123)$, totaling 214. It contains 111 selected vertices in 13 components. Its extension to a complete snake is unknown. The witness establishes that the ordinary local conditions are feasible; it does not establish sharpness of 120.

The independent CP-SAT model rejects share at most 95. The separate tagged CNF model has native refutations at caps 95 and 119, both checked by DRAT-trim. The cap-119 core has 7,534 clauses, including empty-square, quotient-counter and share-cap clauses. The subsequent [share proof](share-proof/README.md) completes Lean replay, all 59 clause batches, their composition, and arbitrary-snake normalization, with 72 theorem audits across 99 modules. No new global upper bound is claimed.

## Effect and next priority

Under the candidate, 1,280 transitions of the current eight-case model receive increased weights. Nevertheless, the old potential remains valid and its attaining four-transition cycle is unchanged. Thus the exact minimum mean remains 480 even under this additional premise. Increasing this one window's charge cannot remove the unchanged cycle.

The next priority is to cover the other surviving critical components. The share certificate interpretation is now complete. Ordinary exclusions must be separated from genuine share improvements: native tests exclude representatives 1, 487, 420 and 481 without any share cap; representative 464 remains unresolved. These exclusions are solver evidence only. Representative 0 is the feasible share candidate above.

## Reproduction and evidence

- `scripts/critical.py` and `scripts/verify.py` use the frozen graph, metadata and potential. The graph is a local build artifact; it can be reconstructed from the six-case checkpoint using its recorded model generator and compared against `data/source-proved-model.json`.
- `scripts/screen.py` performs bounded independent CP-SAT probes; `scripts/ordinary.py` performs separate native SAT checks with cycle cuts.
- `scripts/check_witness.py` independently checks adjacency, counts, shares, acyclicity and the complete-neighborhood endpoint budget.
- `scripts/certify_candidate.py 119` regenerates the stronger native candidate. The default cap is 95. Proof generation and checking have bounded runtimes; a timeout establishes no exclusion.
- `scripts/archive_candidates.py --restore` restores or matches the archived CNFs and refutations with byte-hash checks. The original cap-95 archive uses the name `share0`; the generalized generator names new runs by cap.
- `scripts/candidate_effect.py` checks all current potential inequalities and the unchanged attaining cycle under the share-120 premise.

The main manuscript is unchanged pending the scheduled revision. The current checkpoint remains ten Lean-completed count cases, 32 count theorem audits, and 14,143 additional premises for conditional 234.

The new finite comparison in data/conditional-effect.json reduces those 14,143 count premises to 14,142 when the checked share-120 theorem is included. The full global proof still remains pending.
