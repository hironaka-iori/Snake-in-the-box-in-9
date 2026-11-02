# Independent defined-graph potential audit

Both saved potentials satisfy their edge inequality on every key accepted by the actual retained diagram. The enumeration covers all 791 assigned contexts and all 127 shared acceptance classes. It finds exactly 4,947,008 accepted keys, all present in the saved milestone72 graph: **zero extra keys, zero missing keys**. This equality is a computational result, not a Lean theorem.

| Profile | Slope | Potential range | Checked edges | Minimum slack | Tight edges |
| --- | ---: | ---: | ---: | ---: | ---: |
| Completed | 483 | 551 | 4,947,008 | 0 | 1,288,037 |
| Conditional 012034 floor18 | 496 | 602 | 4,947,008 | 0 | 1,828,136 |

For every accepted full key `(d,q,c)`, the checker verified the exact integer inequality

$$
w_F(d,q,c)+\pi(U(d,q,c))-\pi(V(d,q,c))-P\ge0.
$$

It also checked that each potential has 1,601,856 entries, minimum 0, and maximum equal to its stated range. The final successful numerical run took 1.141 seconds. No solver or compiler was invoked, and no new potential was sought.

The acceptance diagram was read directly from `88-retention-diagram-certificate/lean/GraphData.lean`. The class roots and context assignments were read directly from `92-full-witness-batch/lean/BatchContextData.lean` and `ContextAssignmentData.lean`. Their literal tables agree exactly with the saved DAG JSON: 3,981 nonterminal rows, 127 roots, and 791 unique block assignments. All 46,656 six-symbol codes were evaluated for every class, using the six-digit evaluation and constant-leaf behavior of `CoverTree.lean`. Every accepted code was then evaluated separately in each assigned context. Missing block assignments reject by the defined graph's construction.

The weight evaluation follows `Snake9.Weights98.weight` in `CombinedWeights98.lean`. It parses the geometric table, all 55 concrete history-rule signatures/caps/credits, the five conditioned rules including share120 and their reversals, and the completed/conditional floor clauses from their Lean sources. Direction tables and history prefixes are likewise parsed from Lean and checked against their historical JSON tables. The endpoint computation preserves the full key, canonical source/target shape, longest matching history prefix, and raw state numbering. All endpoints agree with the old graph on the full intersection. Both complete reconstructed weight hashes agree with the earlier certificates.

Exact raw potential hashes are:

- Completed: `90ee55c9e675275f506b947223e36cfeddafc3fcb0a56d61122a5d3ab81e35a0`.
- Conditional floor18: `04effe853d3846049e1a300f90404a4a66df79498586a34d2aa92a1a5f0bb4b8`.

The accepted full-key hash is `ee651c89ee05e2872134ebb259accf26a44e13c27b5eec0532c902f57b55ceae`, using little-endian int64 values `((75*d)+q)*46656+c` in increasing context/code order. The empty extra-key hash is `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.

`data/defined-potential-audit.json` records all 49 input-file SHA-256 values, per-class accepted-code hashes and counts, all 791 context counts and minimum slacks, both full weight hashes, the checker hash, and the absence of any violating key. Input bytes were rechecked at completion. The reproducible checker is `scripts/audit_defined_potentials.py`.

One preliminary run stopped at an overly strong metadata assertion: the DAG metadata pins only the three key columns, whereas the source graph metadata also pins endpoints and weights. Their three common hashes agree. The corrected check compares the key columns explicitly and checks the remaining columns independently. That preliminary attempt took 1.67 seconds of command wall time and stopped before potential evaluation. No mathematical counterexample occurred; all numerical execution was far below the five-minute budget.

The next step is a Lean certificate for the same defined-key inequalities and range bounds, using the already established weight and actual-key bridges. The conditional profile still retains its five local refutation premises, including cap 17 for the 012034 floor18. These Python checks do not remove those premises or establish an unconditional global snake bound.
