# Six-count sum probe review

The audit passed for the three saved probes, their case files and source hashes, reconstructed full-cube formulas, repeated-literal semantics and every saved cycle cut. It ran no solver, compiler or certificate replay. Detailed evidence and reconstructed formula hashes are in `data/six-sum-probe-audit.json`.

All three probes use the seven-transition word $0123042$, window $[0,1,3,7,15,14,30,26]$, radius nine and all six count bounds $[0,21]$. The encoded domain is all 512 cube vertices. The ordinary and tagged base clause lists coincide; the full-cube degree and endpoint constraints apply throughout the cube.

For each internal centre, the two incident path coordinates are excluded, leaving 21 corner literals. Concatenating the six lists gives **126 occurrences and 106 distinct negative primary literals**: 86 vertices occur once and 20 occur twice. The sorted list preserves this multiplicity. A separate sequential-counter reconstruction matches the generated sum clauses and variable allocation exactly. Deduplicating this list would change the intended sum and is not justified.

| Probe | Saved status | Solver seconds | Initial/new cuts | Variables | Recorded clauses | Reconstructed final clauses |
|---|---|---:|---:|---:|---:|---:|
| Total at most 24 | `UNSAT_UNCERTIFIED` | 13.766 | 0 / 4 | 5,072 | 101,898 | 101,902 |
| Total at most 25, first run | `UNKNOWN` | 30.062 | 0 / 13 | 5,198 | 102,149 | 102,162 |
| Total at most 25, resumed | `UNSAT_UNCERTIFIED` | 34.313 | 13 / 6 | 5,198 | 102,162 | 102,168 |

The nominal limits were 30, 30 and 60 seconds, with 1,000-conflict calls and respectively 282, 537 and 596 calls. These are pinned execution records, not independently reproduced timings or solver outcomes. The small overrun in the first cap-25 run is consistent with checking the time between limited solver calls.

The recorded `clauses` field counts the formula stored before newly discovered cuts are added directly to the solver. The resumed formula already contains the 13 inherited cuts, so only its six new cuts must be added to obtain the final count. A future certificate must use the reconstructed final formula or another explicitly checked valid subset, rather than assume the recorded count includes every saved cut.

The resumed case pins the original cap-25 record by hash and preserves its directions, bounds, positions, cap and radius. Its first 13 cut lists equal the earlier lists in order. All **36 cut records, representing 22 distinct vertex sets**, are nonempty, have distinct cube vertices and have minimum internal degree at least two under direct Hamming-distance-one adjacency. Such a finite graph contains a cycle and cannot be a subgraph of an induced path, so every saved cut is a valid necessary restriction on snakes.

All three `selected` fields are null. Their census count tuples are respectively $(2,4,2,4,6,6)$, $(6,6,2,4,3,4)$ and $(5,2,5,6,2,5)$, with totals 24, 25 and 25. Each census's cycle lists form the final batch of saved cuts. These are summaries of the last cyclic models encountered before termination. They are not path witnesses or counterexamples to the negative result. The complete selected models were not saved, so the census count/share values cannot be independently recomputed; only their recorded bounds, totals, share arithmetic and cycle geometry were checked.

The resumed native contradiction supplies evidence for the candidate six-count lower bound 26, stronger than the cap-24 probe's candidate 25. It does not establish that lower bound as a Lean theorem. A complete contradiction certificate, multiplicity-preserving semantic justification, actual-snake transfer and any graph/charge application remain separate obligations. No additional hypothesis or global bound was introduced by this audit.

Evidence hashes:

- `data/six-sum-probe-audit.json`: SHA256 `a0f7fdd20ca4d60e55f4a265f970c88c68f4d95660ef6bfdc995fe12b196a6ab`.
- `scripts/audit_six_sum_probes.py`: SHA256 `e03fb724c84d8c870395b6d44594dcea1f337736c6aac4529ea37c038994eaf6`.

The audit script prints a summary by default and creates a new evidence file exclusively when `--output` is supplied. Existing probe records and audited files were unchanged.
