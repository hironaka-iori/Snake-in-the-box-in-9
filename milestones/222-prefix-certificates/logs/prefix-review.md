# Round 222: frozen first-stage prefix audit

The interrupted ledger and its first continuation pass the independent saved-record audit. All 77 certificate records were checked: 74 new queries and three inherited exclusions. Coverage is complete to the saved stopping points. At root 0, every branch is excluded. At root 78, the only unresolved prefix is

\[
[78,206,198,196,197],
\]

with exact upper bound \(47321233/500000=94.642466\). This bound does not exclude a 93-edge partner and does not supply a feasible point or actual path.

## Coverage and prefix premises

Literal Hamming-distance-one enumeration gives the first neighbours

\[
\begin{aligned}
0 &: 2,4,8,16,32,64,128,\\
78 &: 14,74,76,79,94,110,206.
\end{aligned}
\]

These lists agree with the frozen model edges and all fourteen initial branches. Every saved prefix has distinct allowed vertices, consecutive Hamming distance one, and no nonconsecutive adjacency. For each of the 25 expanded nodes, the audit independently enumerates every allowed neighbour of its last vertex that is unused and adjacent to no earlier prefix vertex. The stored child list is exactly this enumeration. Every noninitial node has exactly one parent; no child is omitted or duplicated.

An actual 93-edge induced path has a next vertex at each saved prefix, since their depths are at most four. Inducedness and injectivity force that next vertex into the corresponding enumerated child list. For each nonroot prefix vertex, the appended row sets its selection variable to one. For every such vertex with a free-endpoint variable, a second appended row sets that variable to zero. This is valid even for the current last prefix vertex: its position is less than 93, so injectivity prevents it from being the full path's final endpoint. Even vertices have no endpoint variable. No universal endpoint restriction is imposed beyond the proper-prefix condition.

The generic `Prefix222` source separately expresses these facts. This audit does not compile it or assert a complete Lean assembly of the concrete tree and numerical certificates.

## Exact certificates

Each new certificate's base-model hash, source hash, prefix and ordered appended rows were reconstructed. The three inherited certificates use their original single first-vertex selection row; their identities match the frozen round-221 first-step audit. Every sparse row-weight list has distinct valid indices, signed equality weights and nonnegative inequality weights.

With scale \(D=10^6\), the audit recomputes all 574 residual coefficients and the weighted right-hand side. The exact upper bound is

\[
\frac{\sum_i w_i b_i+\sum_j\max(r_j,0)}{D},
\qquad r=Dc-\sum_i w_i a_i.
\]

This follows from the row inequalities and variable bounds \(0\le z_j\le1\). Native objective values and numerical optimality are unnecessary. Exactly 51 records are below 94, comprising 48 new exclusions and three inherited exclusions.

| Root | New bound exclusions | Inherited exclusions | Expanded nodes | Unresolved leaves |
|---:|---:|---:|---:|---:|
| 0 | 30 | 1 | 15 | 0 |
| 78 | 18 | 2 | 10 | 1 |

## Interruption and continuation

The original run remains `INTERRUPTED`, exit 1, reason `LOW_FREE_MEMORY`. Its 45 completed queries left 68 nodes and 20 queued prefixes. The minimum sampled free memory was 729,362,432 bytes. No successful-batch status or missing summary is inferred.

The audit reconstructs the first ledger byte for byte from the saved query records, certificates and deterministic expansion rules. All 48 completed nodes, including the three inherited exclusions, remain unchanged in the continuation. The 20 queued prefixes are processed without omission, nine additional nodes are created, and 29 additional queries produce the final 77-node ledger. That ledger is also reconstructed byte for byte. The continuation is terminal with exit 0, 74 cumulative queries and an empty processing queue; its one unresolved depth-limit leaf remains explicit.

The first reviewer byte comparison assumed LF line endings. Semantic reconstruction had already passed; correcting the comparison to the producer's Windows CRLF serialization made the byte comparison pass. This was a reviewer serialization error. No producer evidence was changed.

All source, model, certificate, ledger, summary and stream hashes checked by this review are in `data/prefix-audit.json`. The completed individual certificates survive the resource interruption because their arithmetic and coverage are independently checked. No solver, compiler, search worker or software tests were run.

These files freeze the first-stage result. Deeper continuation requires a separate receipt. This stage excludes 93-edge partners at root 0 and reduces root 78 to one prefix, within the fixed saved-parent model. It does not give a complete two-root exclusion or alter the global snake bounds.
