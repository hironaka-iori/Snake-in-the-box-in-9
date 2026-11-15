# Round 222: completed fixed-parent prefix exclusion

The separate deeper audit passed. The frozen first-stage tree has been extended to 80 nodes, comprising 27 expanded nodes and 53 excluded leaves, with no unresolved leaf. Within the allowed graphs for roots 0 and 78 of the saved 98-edge parent, the complete prefix cover excludes every 93-edge induced partner.

## The three additional certificates

The previously unresolved prefix \([78,206,198,196,197]\) has exactly one allowed induced continuation, vertex 213. Its resulting prefix has exactly two allowed next vertices, 215 and 221. These lists were recomputed directly from the frozen vertices and Hamming distances, including distinctness and absence of chords to earlier prefix vertices.

| Additional prefix ending | Exact upper bound | Result |
|---|---:|---|
| \(\ldots,197,213\) | \(1183031/12500=94.642480\) | Expanded |
| \(\ldots,197,213,215\) | \(3759179/40000=93.979475\) | Excluded |
| \(\ldots,197,213,221\) | \(46707409/500000=93.414818\) | Excluded |

For each new certificate, the audit reconstructs every appended selection row and proper-prefix nonendpoint row, checks the source and base-model hashes, and recomputes the signed equality/nonnegative inequality weights, all 574 residual coefficients, weighted right-hand side and exact upper bound. The two depth-six bounds are strictly below 94 selected vertices. Numerical objective values and numerical solver optimality are unused.

The certificate-producing and candidate-enumeration functions have the same syntax trees as the first-stage source. The deeper source changes initialization, output paths and the permitted prefix depth; the necessary constraints are unchanged.

## Complete coverage and preserved evidence

The prior 77-node ledger is pinned to the frozen first-stage audit. All 76 previously completed nodes remain unchanged. The sole old pending leaf becomes expanded, retaining its certificate and other fields. Exactly three new nodes and three queries are added, giving 77 cumulative queries. The new ledger is independently reconstructed byte for byte from the old ledger and saved output records.

All 27 expanded nodes' child lists were recomputed, including the inherited nodes. Every noninitial node has exactly one parent, and all fourteen initial first-neighbour branches remain present. Thus no next-vertex possibility is omitted or duplicated. Every terminal leaf has an exact upper bound below 94.

| Root | Nodes | Excluded leaves | Largest leaf bound | Margin below 94 |
|---:|---:|---:|---:|---:|
| 0 | 46 | 31 | \(9396307/100000=93.963070\) | \(3693/100000\) |
| 78 | 34 | 22 | \(93984077/10^6=93.984077\) | \(15923/10^6\) |

The maxima occur at prefixes \([0,32,48,112,120]\) and \([78,76,92,84]\), respectively. Expanded-node bounds are excluded from this calculation because only terminal leaves provide the final cover.

## Mathematical consequence and scope

Any actual 93-edge path follows one initial neighbour and then one listed child at each expanded prefix. Each saved prefix is proper, since its depth is at most six. Its selected vertices satisfy the appended selection equations, and injectivity makes every nonroot prefix vertex distinct from the full path's final endpoint. The terminal leaf containing that path would therefore have at least 94 selected vertices, contradicting its checked bound.

An admissible partner longer than 93 edges would have an admissible 93-edge prefix. Consequently every partner at either of these two fixed roots has at most 92 edges. A one-crossing join with this saved 98-edge parent therefore has at most

\[
98+1+92=191
\]

edges. This conclusion uses the previously reviewed necessity of the frozen model constraints for actual partners. It is restricted to this parent and these root configurations. It does not exclude other parent snakes, different join constructions or longer snakes in general, and does not change the global bounds.

## Verification status

The deeper execution is terminal with exit 0 and no resource stop: elapsed 0.734 seconds, peak sampled private memory 27,496,448 bytes and minimum sampled free memory 1,081,765,888 bytes. Its source, model, input-ledger, summary and stream hashes match. The initial resource interruption and both earlier ledgers remain untouched.

The saved `Prefix222` receipt reports three accepted generic theorems, each using only `propext` and `Quot.sound`. This audit matches the source, compiler-log and object hashes and inspects the theorem statements and reported axioms. It runs no compiler. Those generic results remain separate from an end-to-end Lean assembly of the concrete 80-node cover and weighted certificates.

The audit ran no optimizer, search worker or software tests. It reused the frozen first-stage exact-certificate audit, checked all three new certificates, and independently rechecked the complete finite child coverage. The evidence hashes and detailed arithmetic are in `data/deep-audit.json`. All first-stage and deeper audit files are now frozen.
