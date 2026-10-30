# Milestone 71: reduce conditional proof obligations using proved rules

**Completed conditional optimisation round.** Integrating the forty recovered proved restrictions of milestone 70 reduces the selected additional count premises for the conditional bound 234 from **18,788 to 14,155**, a reduction of **4,633 (24.66%)**. The unconditional interval remains **191 <= a(9) <= 235**. No new global bound is established.

The retained selection uses the earlier potential. Recomputing the exact minimum mean improves the numerical model, but the new potential needs more count premises. The smaller proof plan is therefore retained.

## Comparison

All current comparisons start from the 4,997,518-transition proof-supported model of milestone 70. It contains forty recovered proved restrictions, the union of 1,378 contributor reference keys, and checked empty-square share rules. The additional numerical count basis has 25,279 keys. Symbol six always means an actual count between six and 21.

| Certificate | Additional selected keys | Retained transitions | Potential slope | Potential range |
|---|---:|---:|---:|---:|
| Milestone 69, before recovered rules | 18,788 | 4,028,578 | 14387/29 | 18984 |
| Recovered rules, earlier potential | **14,155** | **3,533,981** | **14387/29** | **18984** |
| Recovered rules, recomputed potential | 16,077 | 3,427,221 | 1489/3 | 1897 |

Potential ranges are in the integer units of their respective denominators. Every row supplies the conditional integer bound 234. Least-cover claims fix the potential, candidate basis and comparison graph; they do not establish globally minimal proof cost.

The retained 14,155 keys comprise 16 four-count keys, 1,096 five-count keys and 13,043 six-count keys. They form a subset of the previous selection. All clauses of negative transitions after proved pruning form a subset of the previous clauses. Every selected key has a surviving negative transition containing that key and no other key in the candidate basis. Consequently each selected key is mandatory for this fixed-potential cover, and their union covers every negative transition.

Removing 4,633 obligations from this sufficient proof plan does not prove those 4,633 count keys individually impossible.

## Conditional bound

The retained certificate uses

\[
W+4200m\le1098960,
\qquad
14387(m-8)\le29W+18984.
\]

Eliminating W gives

\[
136187m\le32003920.
\]

At m=235 the left side exceeds the right side by 25. Thus the conditional integer conclusion is m<=234. The selected count premises, arbitrary-snake history interpretation, and complete Lean graph-potential replay remain outstanding.

## Recomputed full conditional model

Applying every additional basis key to the proof-supported graph leaves **3,310,982 transitions**. An integer potential checked on every transition and an attaining twelve-transition cycle establish the exact finite-model mean

\[
\mu=\frac{1492}{3},\qquad \frac{\mu}{120}=\frac{373}{90}.
\]

The potential range is 1897. Its boundary consequence is

\[
14092m\le3310713,
\qquad m\le234.
\]

Relaxing the numerator to 1489 still excludes 235, with margin 226, and gives the third row of the table. Numerator 1488 is insufficient with this denominator and range. Even range zero at the exact mean 1492/3 cannot exclude 234 under the current boundary budget, so this model does not support a conditional bound 233.

The new exact mean exceeds the previous 14392/29, but its sufficient potential requires 1,922 more six-count keys than the retained certificate. This comparison shows why proof-obligation count must be evaluated separately from minimum cycle mean.

## Verification and scope

- `data/old-verification.json` independently matches the count basis, checks all 3,533,981 retained inequalities, and verifies all 14,155 mandatory witnesses. The source graph is pinned to the separately reconstructed milestone-70 enriched graph.
- `data/verification.json` gives the corresponding checks for the recomputed potential, covering 3,427,221 retained transitions and 16,077 mandatory witnesses.
- Both verifiers reconstruct the full-basis filter independently, check every full-model potential inequality, and check the attaining cycle. They reuse the previously verified underlying geometry and transition graph.
- `data/comparison.json` checks that the retained selection and clause set are subsets of their milestone-69 counterparts.
- `data/lean-audit.json` records eight successful theorem audits. Lean checks the generic preservation of a cover under pruning, inclusion in an earlier cover, the conditional arithmetic, and the limitation for 233. Concrete catalogue enumeration and the full graph potential have Python checks, not a completed Lean replay.

No numerical-only share bound is introduced. Remaining count keys are premises unless separately discharged by existing or future proofs. The term proof-supported describes local rules and their saved proof support; it does not assert that the full arbitrary-snake assembly is complete.

## Reproduction and next step

Run `scripts/build.py`, `scripts/analyze.py`, then `scripts/select.py` and `scripts/verify_selection.py`. Run the latter two again with `--old` for the retained certificate. Run `scripts/compare.py`, `scripts/replay.py --resume`, and `scripts/audit_lean.py` for the comparison and Lean receipts. Omit `--resume` for a first Lean build. Generated graph arrays and compiled objects are ignored; the potentials, selections, sources and receipts are retained.

The next round returns to the unconditional proof track: inspect the sixteen remaining four-count premises first, reuse any existing implications, and test their effect on the whole critical family before attempting more expensive six-count proofs. This remains part of the empty-square charging route.

This is round 5 of 10 after manuscript revision 66. Both manuscript sources remain unchanged; the next full rewrite is scheduled for milestone 76. GitHub was refreshed at the start of the round; the reviewed contributor branch remains at `97851813be3cfe0a30ff2694db7b84d1772ce758`.
