# Fixed-mean potential range audit

Bounded mathematical and source review, 2026-11-03. No compiler, graph reconstruction, shortest-path run, potential decoding or heavy computation was performed. Only this report was written.

## Conclusion

All three inspected builders initialize the full potential array to zero and perform synchronous shortest-path relaxation with reduced edge cost `d*w-p`, retaining the previous distance on each iteration. They require convergence, check every edge inequality, and then subtract the minimum. Conditional on the saved runs having executed these exact operations on their pinned graphs, the resulting potentials already have minimum possible global range at the specified mean.

A short extremal directed path would provide an independently checkable certificate of that optimality. Together with the existing all-edge feasible potential, a path whose deficit equals the recorded range proves both directions. This closes a potential-range optimization question at a fixed graph and fixed mean; it does not improve a snake bound, discharge a local-share premise, or justify transferring the result to milestone 92's defined graph without checking the relevant edges and weights there.

## Recorded models and sources

| Mean | Integer scale `(p,d)` | Recorded scaled range | Range in edge-weight units | Builder |
|---|---|---:|---:|---|
| \(483\) | `(483,1)` | 551 | \(551\) | `73-countfree-share-catalogue/scripts/evaluate_checked.py:45–52` |
| \(496\) | `(496,1)` | 600 | \(600\) | `72-four-count-proof-closure/critical-current/scripts/analyze_countfree.py:16–22` |
| \(9259/19\) | `(9259,19)` | 11301 | \(11301/19\) | `83-012034-share-certificate/scripts/compare_target.py:46–53` |

The corresponding metadata files are `73/data/proved-model.json`, `72/critical-current/data/countfree16-all-except012034x20-except012310x12-analysis.json`, and `83/data/assumed-012034x20-model.json`, with full milestone paths pinned below. The first is the completed-local-catalogue comparison; the second is the mixed conditional catalogue; the third explicitly adds the `012034` share-20 assumption. Their mathematical status and their original graph/weight identities must be preserved.

Each builder performs the same update:

```python
pi = np.zeros(N, dtype=np.int64)
nxt = pi.copy()
np.minimum.at(nxt, V, pi[U] + d*W - p)
```

Both right-hand arrays use the old `pi`, so this is a synchronous iteration. A fixed point terminates the loop; exhausting the iteration allowance raises an error. The final assertion is `p + pi[V] <= d*W + pi[U]`, followed by `pi -= min(pi)`. These are full original-state arrays, with `N=1601856`; the temporary cyclic-state compression is used only for mean discovery. The 496 record reports 22 iterations. This review inspected the source and metadata; it did not independently replay their historical execution.

## Sign convention and the mathematical argument

For an edge \(e:u\to v\), define its reduced cost

\[
c(e)=d\,w(e)-p.
\]

A feasible potential satisfies

\[
\pi(v)\leq\pi(u)+c(e),
\qquad\text{equivalently}\qquad
p+\pi(v)\leq d\,w(e)+\pi(u).
\]

For a directed path or walk with \(L\) edges and total weight \(W\), summation gives

\[
\pi(\mathrm{start})-\pi(\mathrm{end})
\geq pL-dW=-\sum_e c(e).
\]

Thus a positive deficit \(pL-dW\) forces a potential drop in the direction of travel. In particular, if a verified path has deficit \(R_*\), every feasible potential on the same graph has global range at least \(R_*\). This holds for real potentials as a mathematical statement; integrality of the competitor is unnecessary.

The all-zero initialization is equivalent to adding a super-source with zero-cost edges to every state. After \(k\) synchronous iterations, the unshifted distance at a vertex is the minimum reduced cost of all walks of length at most \(k\) ending there, allowing every starting vertex and the empty walk. At convergence these are the all-source shortest distances \(\delta(v)\). They are nonpositive, feasible and attained by finite walks. No negative-cost cycle can remain in a graph admitting these finite feasible distances.

Take a walk attaining the global minimum \(\delta(t)\), starting at \(s\). Its reduced total is \(\delta(t)\). Feasibility along that walk gives \(\delta(t)\leq\delta(s)+\delta(t)\), hence \(\delta(s)\geq0\). Since all distances are nonpositive, \(\delta(s)=0\). Consequently \(\max\delta=0\), and shifting by \(-\min\delta\) yields range \(R_*=-\min\delta\). The same attaining walk has deficit exactly \(R_*\), proving minimality of that range.

The equivalent order argument is that any feasible potential normalized to have maximum zero is pointwise at most these shortest distances. Its minimum is therefore no greater than \(\min\delta\). Either argument applies to arbitrary finite directed graphs with feasible reduced costs; no novelty claim is made.

## Small independent certificates to extract next

Do not rerun or verify the entire shortest-path algorithm merely to establish range minimality. Extract a finite path and check its edges and sum independently. The required identities are:

\[
483L-W=551,\qquad
496L-W=600,\qquad
9259L-19W=11301,
\]

for the respective graphs, never mixing their weight columns.

A practical extraction method uses the saved shifted potential. Keep directed edges satisfying equality `p + pi[V] == d*W + pi[U]`. Search this tight-edge graph from all vertices with `pi == R` to any vertex with `pi == 0`. A breadth-first predecessor search avoids cycles caused by zero reduced-cost cycles and gives a simple path. Telescoping on such a path gives the required deficit automatically; the independent verifier must still check every full-key edge, incidence, weight and the integer sum directly. It must include transient vertices and must not restrict the search to the cyclic subgraph used by Howard's algorithm.

For finite-graph evidence, save the original edge indices and complete `(direction,history,count_code)` keys, endpoints, weights and potential values with graph/weight/potential hashes. For a theorem about the newly defined proof graph, verify each full key's block/diagram membership and its defined weight there. Equality of endpoint pairs alone does not identify a weighted edge.

No extremal paths for these three exact models were located or extracted in this review. If the builders and records correspond as intended, such paths must exist. Failure to find them would indicate a provenance, scaling, tight-edge or graph-selection mismatch requiring investigation, rather than grounds to assume the paths.

## Minimal Lean interface

Reuse `Snake9.CriticalFamily61.path_bound` from `61-critical-family-share/lean/FinitePotential.lean`. A small proposed consequence for the native integer-scaled certificates is:

```lean
theorem witness_forces_range
    (p d n Rstar R : Nat) (pi f w : Nat → Nat)
    (hstep : ∀ i < n,
      p + pi (f (i+1)) ≤ d*w i + pi (f i))
    (hspan : pi (f 0) ≤ pi (f n) + R)
    (hwitness : n*p = d*(∑ i ∈ Finset.range n, w i) + Rstar) :
    Rstar ≤ R := by
  have h := Snake9.CriticalFamily61.path_bound p d pi f w n hstep
  omega
```

This is a proposed proof, not compiled during the review. It avoids natural-number subtraction and needs only a difference bound between the two witness endpoints. A global range bound implies `hspan`. Edge membership plus the competitor's feasible-edge premise supplies `hstep`; exact finite data supplies `hwitness`. The existing `edge_of_check` can establish individual inequalities for a particular checked potential. To quantify over all rational or real competitors directly, port the same short telescoping induction to `ℚ` or `ℝ`, or state a rational corollary after clearing denominators. The natural-number signature alone should not be described as directly quantifying over real potentials.

The full shortest-distance characterization is unnecessary for this minimal certificate. A feasible potential with range \(R_*\) supplies the upper side, and the finite witness plus this lemma supplies the lower side. A witness certificate without a full feasible-potential check proves only the range lower bound.

## Existing local results and limits of the conclusion

Milestone 74 already contains relevant prior work. `lean/PotentialRangeObstruction.lean` proves the conditional rational algebra `path_deficit_obstruction`. Its `optimization/catalogue_test.py` performs all-zero shortest-walk relaxation with layered predecessors, reconstructs walks, and independently checks their edges and sums. `optimization/README.md` explains six weakened-catalogue obstructions using a mean-496 cycle and walks of length 7–17 with deficits at least 632. These are useful extraction/verifier templates, and they already show why a path deficit can obstruct changing a potential. They are not extremal-range certificates for the three models above.

A bounded text search of milestone Lean/source/notes, the paper and `work/spectral` found no existing generic fixed-mean shortest-distance range-optimality theorem or saved current-model extremal paths. This is a bounded local result, not an exhaustive claim about external literature or every generated source.

Range minimality at one fixed mean does not by itself optimize the boundary objective over all possible means. The existing objective in unscaled units is \(227\mu-R(\mu)\). A verified extremal path of length at most 227, together with an attaining cycle that caps the mean by the current \(\mu\), would also bound that objective for every smaller feasible mean. The 496 record's 22 synchronous iterations suggest an attaining minimum-distance walk of at most 21 edges under the inspected loop convention, but this still needs an explicit checked witness before use. This observation should be treated as a possible short extension of the certificate, not as a new completed theorem.

Changing the graph, its weights, permitted endpoint states or boundary accounting can change the result. A path in a relaxed graph need not be realizable by an actual snake. Improved restrictions on actual start/end states may reduce the relevant boundary loss even when the unrestricted global potential range is optimal. All reference-catalogue, pending local-share, actual-credit and full defined-graph potential obligations remain explicit.

## Joint optimality of the constant-slope/range comparison

The following bounded algebraic extension was checked by symbolic reasoning only. It has not been compiled in Lean, and no concrete extremal path is supplied by this audit.

Fix the graph and its weights. Suppose an edge-potential certificate has slope \(M\) and range \(R\), and a certified directed cycle has mean \(M\). Suppose also that a certified path has \(k\) edges and total weight \(C\), with

\[
R=kM-C.
\]

All quantities here use unscaled edge-weight units. In particular, the single-target model uses \(M=9259/19\) and \(R=11301/19\). Define the attained comparison value

\[
B_*=\frac{1098960+8M+R}{4200+M},
\qquad 4200+M>0.
\]

Let another feasible potential on this same graph have slope \(\mu\), global range \(\rho\), and \(4200+\mu>0\). The cycle bounds \(\mu\leq M\). Summation along the specified path gives \(\rho\geq k\mu-C\). If

\[
k+8\leq B_*,
\]

then its comparison satisfies

\[
\frac{1098960+8\mu+\rho}{4200+\mu}\geq B_*.
\]

Indeed, the baseline identity gives

\[
1098960-C-4200B_* = -(k+8-B_*)M.
\]

Consequently,

\[
\begin{aligned}
1098960+8\mu+\rho-B_*(4200+\mu)
&\geq 1098960-C-4200B_*+(k+8-B_*)\mu\\
&=(k+8-B_*)(\mu-M)\\
&\geq0.
\end{aligned}
\]

Both factors in the last product are nonpositive. Division by the positive competing denominator completes the argument. No extra nonnegativity assumption on \(\rho\) is required by this algebra, although an actual range is nonnegative.

The exact recorded comparison values give these sufficient path-length thresholds:

| Mean \(M\) | \(B_*\) | Sufficient integer condition |
|---|---|---|
| \(483\) | \(157625/669\) | \(k\leq227\) |
| \(496\) | \(137941/587\) | \(k\leq226\) |
| \(9259/19\) | \(20965613/89059\) | \(k\leq227\) |

The threshold for mean 496 is 226 because its comparison value is strictly below 235. This criterion optimizes the exact quotient; it is stronger than merely ruling out a particular integer threshold using \(227\mu-\rho\).

A minimal additional rational Lean lemma can accept the identities `R = k*M-C` and `1098960+8*M+R = B*(4200+M)`, the inequalities `mu ≤ M`, `k+8 ≤ B`, `k*mu-C ≤ rho`, and `0 < 4200+mu`. Multiplying the two nonpositive differences proves the cross-multiplied conclusion, followed by division by the positive denominator. Keeping the baseline as an equality avoids unnecessary quotient manipulation in the core lemma. The graph-specific cycle and path certificates supply its hypotheses independently.

If the existing feasible potential and such a short tight path are checked on the chosen defined graph, the current \(B_*\) is therefore the best value obtainable from any feasible constant slope and global potential range on that fixed graph with these same budget constants. This does not prove that an extremal graph walk is an actual snake, that the graph model is optimal, or that \(B_*\) is the true snake bound. It supplies no novelty claim and leaves all reference, local-credit, potential and actual-snake obligations unchanged.

## Reviewed hashes

Paths are relative to `E:/Snake-in-a-box/milestones/`.

| Artifact | SHA-256 |
|---|---|
| `73-countfree-share-catalogue/scripts/evaluate_checked.py` | `be1a41ac42427c02f61007b1b7e62983bc248880827505e0481e25473ddbd29d` |
| `73-countfree-share-catalogue/data/proved-model.json` | `785956145396df7cf6230c446a9e7469b7c4b1713c6cf70d21a9091f1c8f7907` |
| `72-four-count-proof-closure/critical-current/scripts/analyze_countfree.py` | `bbc7952ae4c2ccf9bd68ad1cf809502585affa4991b28ca21dc7d584b8652036` |
| `72-four-count-proof-closure/critical-current/data/countfree16-all-except012034x20-except012310x12-analysis.json` | `3a74e090001154ab77ec513c2dcbaf7e9cb9ad0733eb768470d563b63f3fcde2` |
| `83-012034-share-certificate/scripts/compare_target.py` | `b30e53f2639f0aee17f953b955eac357557998192d515296ed9546cdd52c0d48` |
| `83-012034-share-certificate/data/assumed-012034x20-model.json` | `f64ad918df0c725b3773b5f6f896162af4ea8044ab031489812076d0ca037a85` |
| `61-critical-family-share/lean/FinitePotential.lean` | `7dfbe61e69208dce373f4a18faeedadeb904c85a39027c9df8ae7a0a86fd716a` |
| `74-graph-interpretation-audit/lean/PotentialRangeObstruction.lean` | `dca1085d17bda5cfeae52be85c7f9a840936362f839672f053a26cd782b52830` |
| `74-graph-interpretation-audit/optimization/catalogue_test.py` | `86c5377fe3bd47b07b557eb84c4954bb025c83fbc8d16e220dac1e7a97ce1978` |

The recorded decompressed potential hashes are respectively `90ee55c9e675275f506b947223e36cfeddafc3fcb0a56d61122a5d3ab81e35a0`, `99e727974a6e0bb840e80c30f18845473cd21f3f8feacfab87f7d427509ebf0a`, and `420c0e6117d0edf3f76453d153913b4802b7ba2ec38a608ddb0329a4e01fc885`. These were read from metadata; the potential arrays were not rehashed or decoded in this audit.
