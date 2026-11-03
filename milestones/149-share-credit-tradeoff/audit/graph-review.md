# Independent audit of the fixed-graph credit obstruction

The selected rows pass an independent source-array audit. The new 28-edge walk is valid in the original 4,947,008-edge graph, has weight 13280 and has no occurrence events. The three-cycle has total 1488 and no events. The eleven-cycle has total 5452 before credit and four events. No graph search, Lean process or solver was run for this audit.

The complete record, including every selected row, all six count symbols, decoded directions, input hashes and before/after input checks, is `graph-review.json`, SHA256 `29c1a4af5863eea9b8144953b4dc3b152368c2a86c744dccc8091c0c2507f418`.

## Reconstruction

The source is `milestones/72-four-count-proof-closure/critical-current/build/source-graph.npz`, SHA256 `b40f1ca44ad8f3269f890efe8decc60f19dabd647f11255c05df3727341c2c34`. All six arrays used here, `U`, `V`, `weight`, `direction`, `history` and `count_code`, were hashed against `source-proved-model.json`. Only the 39 distinct rows used by the two cycles and walk were retained for calculation.

For each row, the six symbols were decoded as base-six digits plus one, in chronological order. Its shape is the smaller of the canonical final six directions and their canonical reverse. Its weight without credit was reconstructed as the maximum of the saved base weight and 120 times the entering symbol plus the specified shape floor. Every stored field in the new walk agrees with the reconstruction, and consecutive endpoints agree.

The event is exactly the current implementation: canonical suffix 012032, symbols at chronological indices 2 and 4 both below 6, and their sum at most 9. A symbol 6 denotes an actual count at least 6. It does not certify the event even when some represented actual counts could have sum at most 9. No clipped symbol was interpreted as an exact count of 6.

The fixed floors are `(16,15,18,16,16,12,16,16,16)` in the order 012031,012032,012034,012301,012304,012310,012314,012340,012345. The only variable charge is the same uniform nonnegative credit per occurrence, with allowance 24.

The eleven-cycle weights before credit are

\[
375,496,495,496,496,376,616,495,496,495,616.
\]

The 28-edge walk weights are

\[
252,498,376,376,616,736,375,256,735,496,376,496,736,375,
256,735,496,376,496,736,256,376,736,615,376,375,496,256.
\]

Six walk rows have suffix 012032. Each has at least one of the two tested count symbols equal to6, so every one fails the exact-symbol event test. This is a statement about the graph's event indicator, not an assertion that the actual pair count must exceed9.

## Exact consequence

Any potential slope \(\mu\ge0\), range \(R\), and credit \(C\) for this fixed graph satisfy

\[
\mu\le496,\qquad 11\mu\le5452+4C,\qquad 28\mu\le13280+R.
\]

Consequently,

\[
24C\ge66\mu-32712,\qquad R\ge28\mu-13280,
\]

and

\[
1098960+8\mu+24C+R-235(4200+\mu)
\ge65968-133\mu\ge0.
\]

The comparison therefore remains at least 235 for every credit. The three scalar constraints attain equality at \(\mu=496,C=1,R=608\). This proves sharpness of the displayed arithmetic relaxation only. It supplies no full-graph potential and no snake construction. The parent is separately responsible for the Lean arithmetic receipt.

## Graph boundary and limitations

This audit concerns the original full97 graph. The later 144 retained graph removes walk positions 4,5,27, with original edge IDs 567947,4335674,2211193. It also removes two edges of the three-cycle, IDs 1131395 and17417. The eleven-cycle survives. Thus this particular three-constraint obstruction cannot be transferred unchanged to the later graph.

The saved 69-edge012032 obstruction has 65 removed row occurrences in the later graph; the saved 77-edge012340 obstruction has 3. Their earlier full-graph necessity statements must also retain their original scope.

The global boundary budget, all other floors and the definition of the occurrence event remain fixed. Different graph restrictions, more informative count states, a charge on a different event or stronger boundary accounting are outside the result. No improved global upper bound, global optimality claim or novelty claim is made.
