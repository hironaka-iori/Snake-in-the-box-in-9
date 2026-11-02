# Independent review of the three cycle/path certificates

Review date: 3 November 2026, Japan time. Result: all three supplied finite-model certificates passed the independent numerical checks described below. No Lean compiler, BFS, or extraction routine was run. This review does not substantiate the certificates' `shortest_tight_path` field.

## Exact results

Let the potential inequality be $P+\pi(v)\le D w+\pi(u)$. The reported range in the following table is the range of the integer potential; the normalized range is that number divided by $D$.

| Profile | Cycle length / weight | Mean $P/D$ | Path length / weight | Integer path deficit $Pk-D S$ | Comparison bound | Integer comparison |
| --- | --- | --- | --- | ---: | --- | ---: |
| Completed local floors | $4/1932$ | $483$ | $9/3796$ | 551 | $157625/669$ | 235 |
| Additional assumed 012034 floor 20 | $19/9259$ | $9259/19$ | $31/14512$ | 11301 | $20965613/89059$ | 235 |
| Full conditional profile | $3/1488$ | $496$ | $7/2872$ | 600 | $137941/587$ | 234 |

Each cycle closes and has the displayed exact mean. Each path chains from an integer-potential maximum to a minimum of zero. Every listed edge is tight. Thus the paths attain the integer-potential ranges 551, 11301, and 600; the middle profile has normalized range $11301/19$. A shortest-path assertion is unnecessary for this range argument.

The exact unnormalized margins excluding the next integer are 1813 at $m=236$, 52311 at $m=236$, and 32 at $m=235$, respectively. These are finite-model comparisons, conditional on the separate charge interpretation when applied to snakes.

## Independent checks performed

The review used its own Python implementation and did not import or call the extraction script. It checked:

1. Every input-file hash listed in each certificate, the extraction-script hash, and every source-array hash against the pinned source model.
2. The full weight-vector hash after independently reconstructing each profile as the maximum of the pinned source weight and its declared count-free floor. The full conditional vector was reconstructed from its declared shape list and overrides as well. Means, potential ranges, potential hashes, and weight hashes agree with the separately pinned model metadata.
3. The integer potential's full size, minimum, maximum, and decompressed hash. All 4,947,008 edge inequalities were independently checked for each of the three profiles in blocks of 100,000 edges. The resulting tight-edge counts match the certificates.
4. All 73 supplied path/cycle edge occurrences, representing 61 distinct full $(d,q,c)$ keys. Edge indices, direction IDs, histories, count codes, source/target IDs, and potential values match the pinned arrays.
5. Every supplied full key's recorded block/class and six-digit acceptance-DAG traversal, including nonterminal remaining-depth checks. Each traversal reaches terminal true. Source/target pairs were never substituted for full keys.
6. An additional independent reconstruction of each witness's original weight and raw endpoints from the direction words, geometry credit, forward count rules and reversals, all emitted history rules, the share-120 update, and longest-suffix history transition. These reconstructed values match the pinned source arrays before applying the profile's extra floor.
7. Path chaining, cycle closure, exact sums, scaled deficits, comparison fractions, and integer comparisons using exact integer and rational arithmetic.

The source arrays have 4,947,008 rows. The review did not regenerate the reference exclusions, geometry certificates, history catalogue, or acceptance DAG. Their hashes were pinned; their mathematical correctness remains governed by the existing proof dependencies.

## Joint slope/range comparison

The cycle and path witnesses also justify the proposed joint comparison algebra. Fix the same finite weighted graph and the same charge constant $A=1098960$. Let $\lambda\ge0$ be any feasible normalized constant slope, and let $\rho\ge0$ be the global range of a corresponding normalized potential.

A cycle of mean $\mu$ forces $\lambda\le\mu$. A path of length $k$ and weight $S$ forces

$$
\rho\ge k\lambda-S.
$$

The resulting charge comparison is

$$
B(\lambda,\rho)=\frac{A+8\lambda+\rho}{4200+\lambda}
\ge f(\lambda):=\frac{A-S+(k+8)\lambda}{4200+\lambda}.
$$

The supplied path has $\rho_*=k\mu-S$. Direct subtraction gives

$$
f(\lambda)-B(\mu,\rho_*)
=\frac{(\mu-\lambda)\bigl(A-S-4200(k+8)\bigr)}
{(4200+\lambda)(4200+\mu)}.
$$

The three values of $A-S-4200(k+8)$ are respectively 1023764, 920648, and 1033088, all positive. Therefore every feasible slope/range pair has

$$
B(\lambda,\rho)\ge B(\mu,\rho_*).
$$

The certificate's condition $B(\mu,\rho_*)\ge k+8$ is exactly the same sign condition, since

$$
B(\mu,\rho_*)-(k+8)
=\frac{A-S-4200(k+8)}{4200+\mu}.
$$

Its recorded margins are $146252/669$, $17492312/89059$, and $129136/587$; all match the independent rational calculation. The symbolic subtraction above proves the general inequality. Numerical substitutions at five slopes were also checked as an arithmetic consistency check; those substitutions alone would not establish the universal statement.

Because the supplied potentials pass every pinned array-edge inequality and attain $(\mu,\rho_*)$, their comparison fractions are optimal within this fixed finite-graph, constant-slope, global-range, fixed-boundary certificate architecture. Changing the weight profile, graph restrictions, reachable-state set, boundary accounting, or endpoint-specific estimate changes that optimization problem.

## Scope of the conclusion

The mathematical conclusions above concern the pinned array graphs. Every supplied witness key is also accepted by the saved diagram. Consequently, when the defined graph uses the same key weights, these witnesses impose the same necessary cycle/path constraints on its potentials. This review did not prove equality of the full diagram-accepted row set and the array graph. It therefore does not assert that the recorded potentials satisfy any additional diagram-accepted rows.

No witness was shown to be realized by a single snake. The weight-to-five-centre-share theorem, reference-catalogue premises, and any unfinished local-floor certificates remain outside this review. In particular, the additional012034 profile retains its stated local assumption, and the full profile retains all unfinished local-floor assumptions. There is no new unconditional upper bound here.

The machine-readable report is `data/range-certificate-review.json`. It records all three certificate hashes, pinned input hashes, reconstructed weight and potential hashes, checked counts, exact comparisons, and scope exclusions. Its SHA-256 at completion is `6fea38c92d9eedb7f69b4a5ceb4a6053cddca261e416b241b1cf643ad18beefe`.
