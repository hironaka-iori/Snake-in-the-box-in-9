# Scalar weight formula review

Status: `PASS_SOURCE_EQUIVALENCE_WITH_INPUT_AND_HASH_GATES`.

The scalar formula in milestone 156's `review/walk_audit.py` reproduces the shared bonus and final zero-credit weight in `scripts/reconstruct144.py` and `scripts/potential_range.py` for every valid source row, under the pinned direction model, count rules and floor profile. This conclusion follows from the source formulas and their guards. This review did not execute the graph or compare all row values numerically. No additional weight modification was found after the shared bonus is constructed.

## Shared bonus

Let the nine directions be \(d_0,\ldots,d_8\) and the six chronological stored count symbols be \(c_0,\ldots,c_5\). The reconstruction initializes the old bonus to zero, then maximizes the applicable rule credits. Only placement 1 awards credit: its directions are `d[3:9]` and its counts are `c[1:6]`. Placement 0 contributes exclusions but no weight bonus.

For each of the 13 pinned rules, recognition uses the direction shape with reversal allowed. If the forward canonical word differs from the chosen shape, the five counts are reversed. Rule applicability requires the entire stored count interval to lie in each rule interval: a stored 6 has lower endpoint 6 and upper endpoint 21. The demand sum uses the stored symbols, including 6 as the lower endpoint. Every coefficient is 24 because reconstruction supplies `coefficients=[24,24,24,24,24]`.

The resulting old bonus is the maximum of zero and

\[
24\max\left(0,L-\sum_{j\in P}c'_j\right)
\]

over applicable rules, where \(c'\) is the oriented five-count sequence, \(L\) is the rule lower bound and \(P\) its selected positions.

The pair bonus is exactly

\[
B_{\mathrm{pair}}=
\begin{cases}
24\max(0,9-c_2-c_4),&\operatorname{shape}(d_3,\ldots,d_8)=012032,\\
0,&\text{otherwise}.
\end{cases}
\]

Reversing the five counts swaps the two selected positions and leaves their sum unchanged. Crucially, the bonus has no exact-count guard. The conditions requiring counts below 6 belong to the pair exclusion and occurrence indicator. Applying that guard to the bonus would change weights on some valid saturated-count rows.

The six-count bonus is exactly

\[
B_{\mathrm{six}}=
\begin{cases}
24\max\left(0,25-\sum_{j=0}^{5}c_j\right),
&\operatorname{shape}(d_2,\ldots,d_8)=\operatorname{shape}(0123104)
\text{ and }c_0<6,\\
0,&\text{otherwise}.
\end{cases}
\]

The guard uses the first chronological count even when direction recognition uses reversal. The count sum uses stored values; there is no requirement that all six be exact for this bonus. The all-exact condition belongs to the six-count exclusion.

The shared bonus is precisely

\[
B=\max(B_{\mathrm{old}},B_{\mathrm{pair}},B_{\mathrm{six}}).
\]

The extracted reconstruction source assigns `shared` once, at logical line 230. Later code changes the mask, defines the occurrence indicator, and verifies predecessor records. It does not modify any of these three bonus components or `shared`. The historical expressions with factors 3, 12 and credits 83 or 533 occur in predecessor checks. They are not final weight updates.

## Final weight and retained mask

Milestone 156 uses

\[
W=\max\left(w_{\mathrm{source}},
120c_5+\max(F_{\mathrm{suffix}},17\mathbf1_{\mathrm{match}})\right)+B.
\]

The share-17 match checks only the suffix directions and five internal counts, in both orientations. The canonical 012032 counts must lie in
\((4,[0,4],4,[0,5],3)\). Stored 6 cannot match any of these intervals. The two orientations are combined by logical OR, and the new share replaces the floor through a maximum. No uniform occurrence credit is added in the accepted zero-credit run.

The scalar formula does not reconstruct the exclusion mask. Reusing the exact accepted milestone-144 removal list is therefore essential. It carries the prefix tests, interval/sum exclusions, odd-pair rule, hypothetical six-count exclusion and later checked exclusions. Lowering the share floor changes the weight calculation only; it supplies no reason to alter that accepted mask.

Before changing 012034 from 18 to 17, the bounded implementation should reproduce the accepted milestone-156 weight hash over the retained rows in their original order:

`535da1b02972e98280ae059d08f656f0a9aa6d75433f56b9be1fc09eb5961998`

The accepted counts are 4,947,008 source rows, 4,661,572 retained rows and 1,601,856 states. The accepted retained-row-ID hash is

`963283f7593eb2cc3b6d0766ef1e83644f43d2d38c8d60b8bc8f13651eb15f1f`.

Use the same signed 64-bit weight representation and ascending source-row order when hashing. Cast unsigned loaded counts to a signed type before subtraction in demands and pair deficits. A mismatching baseline weight hash is a blocker; the floor-17 experiment must not proceed on such a reconstruction.

## Scope and input checks

No source-level blocker was found. The pinned 13 rules have canonical direction orientation, distinct selected positions and reversal-symmetric selected-position sets. All 505 direction words have length nine and labels at most 8, so the scalar string canonicalization and reconstruction's tuple canonicalization induce the same order. These small metadata checks were executed without loading graph arrays.

The source equivalence does not independently discharge the reconstruction's historical source/proof gates or its inherited mathematical assumptions. Those remain attached to the accepted evidence. The required full baseline weight-hash comparison will test the new loader, indexing, clipping, orientation and output ordering together before the proposed change.

No graph execution, optimizer, solver or Lean process was run. Accepted files were unchanged. Only this new review was written.

SHA-256 inputs:

- `156/scripts/reconstruct144.py`: `17c467c613cd04384e40efd9dc881fd1dee6bff60809696379728464a0a64734`
- Extracted `RECONSTRUCTION` string: `46e919a24c581d616ddfebbbd5c33f5efc8385ac689b69ffe7702883512a2301`
- `156/scripts/potential_range.py`: `1f0c49f85c68a9945269431fd7f40f8e30cba5e4dc8ddad492ecd3b71c0ead51`
- `156/review/walk_audit.py`: `2dd714f8627af1a34226ad9c5d54fe417a68672d2323d4bc553faa8314df166b`
- `120/data/full-rules.json`: `dae2b8fc4c807501037041ffada61d80cda1acbf03a3b4536c84338d444a2f57`
- `59/extended/data/model.json`: `2334325d650cc9b71c0c6ab836183cecd4f1fc4d8b6555f63211592a22a0e2bf`
