# Joint intervening-count bound and excess accounting

For distinct coordinates a,b,c,d,e and the eight transitions `(a,b,c,d,e,c,a,d)` starting at position r, suppose the first and seventh internal singleton counts are both at most three. This milestone proves

\[
\alpha_{r+3}+\alpha_{r+6}\ge12.
\]

This strengthens the sum 10 obtained by adding the two individual lower bounds from milestone 40. The completion gate `data/verification.json` passed **ten Lean dependency audits**, all with the applicable standard axioms only. The paper's global interval remains 191 <= a(9) <= 236.

## Logical chain

1. `MultiCentreCount.lean` proves a general identity: the number of true literals in concatenated opposite-corner lists equals the sum of the corresponding singleton counts. Repeated vertices retain their multiplicity. The theorem applies to an arbitrary list of centres.
2. The ordinary radius-four encoding imposes upper bound 3 at the first and seventh internal centres. The other counts retain their full range 0..21. A joint counter imposes the hypothetical upper sum 11 at centres 3 and 6.
3. The joint counter receives a semantic proof of its actual count bound. Its temporary encoder tag does not make it an endpoint counter: the generated proof separates it from the ordinary counters and applies the checked generic joint-counter soundness theorem.
4. Every retained degree, endpoint, count, and cycle clause is derived from the geometric assumptions. A native refutation is checked, the extracted core is independently refuted, and the latter resolution proof is replayed in Lean.
5. The exact frame-count bridge transfers both counts to an arbitrary snake. Coordinate normalization is proved for any five distinct coordinate labels.

The extracted core has 4097 clauses and 1401 active variables. Its replay has 5222602 resolution hints, divided into 174 segments and 29 check modules. All 208 modules in the recorded replay build completed. Data-module dependencies were built in order, with at most two independent check modules running alongside them. Imported support is reused; this is not a clean rebuild of the entire project.

## Conditional contribution to the charge

Write b_j = min(6, alpha_j) and delta_j = alpha_j - b_j. If a qualifying occurrence also has b_(r+3) + b_(r+6) <= 11, then delta_(r+3) + delta_(r+6) >= 1.

For a set J of such starting positions in a fixed orientation, each position is counted at most twice, once at each offset. The checked counting result gives

\[
|J|\le2\sum_j\delta_j.
\]

Consequently the charge identity gives

\[
G_{12}\ge24\sum_j b_j+12|J|+\sum_x\sigma_{12}(x).
\]

This uses the same excess budget as other excess-based contributions. Independent bonuses cannot be added without a combined multiplicity argument. No positive lower bound on |J| has been proved.

## Controls and limitations

The saved local forest from milestone 40 with counts `(3,5,6,8,10,6,3)` attains joint sum 12. Its degree, endpoint, acyclicity, and singleton counts were independently rechecked here. This establishes sharpness in the local model, without establishing extension to a complete snake.

All 131 published bank paths were independently verified as induced paths. They contain 1442 oriented occurrences of the direction pattern, but none satisfies both low-count hypotheses. These observations supply no positive frequency estimate for the new theorem.

The proposed lower sum 24 over the five intervening centres remains numerical. The general counter lemma now supplies its counting infrastructure, but its contradiction still requires a separate proof replay. The identified low-mean diagnostic cycle was already excluded in milestone 40; no replacement minimum cycle mean has been certified here.

## Reproduction

Run `scripts/certify.py` for the extracted CNF, native checks, and replay-source generation, then `scripts/wrappers.py` for the exact geometric interpretation. Build the generic counter with `scripts/check.ps1`, run `scripts/replay.py`, then run `scripts/check.ps1 -Modules @('JointExcess','SumExcess')` in PowerShell. The local runtime paths are explicit in those scripts.

Run `scripts/bank_controls.py`, `scripts/archive.py --pack`, and `scripts/verify.py` for the final gate. Archived proofs can be restored with `scripts/archive.py --unpack`. No solver-only joint threshold is promoted to a theorem by these instructions; the audit receipts and final gate are required.
