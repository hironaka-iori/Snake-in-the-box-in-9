# One-exchange static enumeration: source review

**Source review: no mathematical defect found in the current zero-start enumeration. Full independent decision reconstruction is prepared but has not yet been executed at this preparation checkpoint.** The separate native Hamiltonian worker owns the resource slot; execution of the full audit requires the parent's explicit authorization after that worker stops.

## Family and indexing

The 145 saved classes each have 96 distinct vertices of one parity. Removing each original vertex leaves a 95-set. The insertion list consists of all 160 same-parity vertices outside the original 96-set, so the removed vertex is not reinserted and every description changes exactly one vertex. The complete labelled family has 145 * 96 * 160 = 2,227,200 descriptions, grouped into 13,920 cores. Different descriptions may give equal final sets; the producer retains them separately and makes no distinct-class or full-symmetry claim.

The global core index follows base order and sorted removed-vertex order. The description index is 160 times that core index plus the ascending insertion-list index. The saved bases have the same pinned bytes as the previously audited round-232 bases. The current arguments use `start_core = 0`.

## Incremental graph updates

For the 95-set, each opposite-colour label is classified by its exact selected-neighbour set. Singleton labels are retained with multiplicity as a bit set per endpoint vertex. Two-neighbour labels are retained with multiplicity as a bit set per unordered endpoint pair. The graph adjacency itself is simple, as required for Hamiltonian-path existence.

Inserting a vertex changes only its nine opposite-colour labels:

- A zero-neighbour label becomes a singleton label supporting the inserted vertex as a contracted endpoint.
- A singleton label at an old vertex becomes an edge joining that vertex to the insertion. The old vertex loses endpoint support only if every former singleton label there is among the affected nine labels. One unaffected label is enough to keep its port.
- A two-neighbour label becomes unusable with three selected neighbours. The old simple edge is removed only if all parallel labels for that pair are affected. If one unaffected parallel label remains, the edge is kept.
- Labels with at least three old neighbours remain unusable.

The source implements these all-label conditions with `portlabels[v] & ~nm` and `edge_labels[t] & ~nm`. Their masks contain actual label vertices, so the comparison with the inserted vertex's neighbour mask is on the correct domain. Multiple affected labels for the same edge or port only repeat an idempotent operation. Edges to the insertion cannot collide with removed old-old edges. The changed-adjacency dictionary preserves all updates already made for a vertex. The inserted vertex is handled separately and is absent from the 95-set adjacency dictionary.

The 95-set is rebuilt from the original selected mask for every removed vertex; no deletion state leaks from a preceding core. All adjacency and support masks refer only to the resulting selected set.

## Static status logic

The priority is isolation, fewer than two supported endpoints, more than two simple leaves, an unsupported leaf, disconnectedness, then candidate. Each exclusion is necessary for a Hamiltonian path on the 96-vertex contraction graph with both endpoints supported by singleton labels. Simple degree, rather than label multiplicity, is used for leaves. The explicit connectedness traversal uses the updated old vertices and the separate new-vertex adjacency.

`CANDIDATE` means that these necessary conditions passed. It establishes neither Hamiltonicity nor a lifted snake. Native Hamiltonian outcomes are outside this static audit.

There is a reuse caveat in the producer's completion label: `COMPLETE_STATIC_COVER` is chosen when `next_core == 13920`. With a nonzero `--start-core`, this can describe only a completed suffix. The present saved run starts at zero and records all 13,920 cores. The independent auditor explicitly rejects a nonzero start for a standalone full-cover claim and checks every core, decision offset, and description count. The caveat does not invalidate this current run.

The producer flushes decisions after complete 160-case cores but saves its progress JSON after whole bases. An interrupted process can therefore leave a binary file ahead of its JSON checkpoint. Such a state must not be accepted as a complete cover. The auditor requires the terminal accepted receipt, exact byte length and hash, and full core/decision correspondence.

## Prepared independent reconstruction

`scripts/audit_exchange.py` does not import the producer or reuse its graph updates. For each actual resulting 96-set, it examines cube labels adjacent to its selected vertices and counts their neighbours by direct intersection with the complete selected mask. Singleton counts determine endpoint support; two-neighbour counts directly form simple adjacency by union. This independently handles all parallel labels. Early exit is allowed only after finding an actual isolated selected vertex, which already fixes the first-priority status.

The inserted vertex is examined first; a core-based priority changes only the order of other vertex inspections. It does not change the exact full-set label counts used for any decision. If no isolated vertex exists, the script completes all degrees and ports, applies the same stated mathematical status priority, and traverses the reconstructed graph for connectivity.

The auditor will compare all 2,227,200 computed codes with `exchange-decisions.bin`, all 13,920 local count records, every saved candidate description, base totals, final totals, progress summaries, and source/input/output/log pins. It will separately count exact equal candidate sets without making a symmetry claim. It contains no optimizer, Lean invocation, or software test. A time limit or mismatch produces an explicitly incomplete/failed receipt rather than a full-cover assertion.

The script requires `--execute` and refuses to start while either the round's native-worker lock or the full-graph lock exists. It has not been executed at this checkpoint. No `data/exchange-audit.json` has been created yet.

## Stable producer metadata and hashes

The producer records `COMPLETE_STATIC_COVER`, 2,227,200 descriptions, and 13,920 cores. Its reported counts are 1,603,284 isolated, 274 insufficient-port, 616,230 excess-leaf, 6,019 unsupported-leaf, 12 disconnected, and 1,381 candidate descriptions. These counts are recorded metadata at this source-review stage; independent full reconstruction is pending.

| File | SHA-256 |
|---|---|
| `scripts/exchange.py` | `8b478ce38211257008ad588757137bfb68a44c65afe6bfb7430b73d4be7bc913` |
| `scripts/run_exchange.py` | `f7e872966f5512129ba2876602c3718e72eb6ab7e086d4032ae71c9d0f14f50b` |
| `scripts/audit_exchange.py` | `0f382159c8a09236e37d1fde2ed21aa86122d44b2cca3ccb21f75e1790b918a0` |
| `data/bases.json` | `ff2356155763cb4bf8f2d1eff80f893021793deca4c76e9183f990ecb6b3297b` |
| `data/exchange.json` | `bf75550ff4760a88713b1c469c7971e2bea75cdac3e77398d92590a7acfb60ca` |
| `data/exchange-decisions.bin` | `b538167ca664ab2e57f66e45480074717cb716831e65182a2045d3564cc5dd4f` |
| `data/exchange-execution.json` | `52bb3e98199e85d06fa8c191b226f2459f666b8e380664ebaeaa71c015c1330a` |

Paths are relative to `milestones/234-single-colour-exchange`. Only the assigned audit script and this report were written. No heavy scan, solver, compiler, software test, or modification of existing evidence was performed during preparation.

## Subsequent full decision-audit execution

Status: `PASS_FULL_INDEPENDENT_STATIC_DECISION_AUDIT`. Verified descriptions: 2227200; completed cores: 13920.

Reconstructed counts: `{"CANDIDATE": 1381, "DISCONNECTED": 12, "FEWER_THAN_TWO_PORTS": 274, "ISOLATED": 1603284, "TOO_MANY_LEAVES": 616230, "UNSUPPORTED_LEAF": 6019}`.

Verified candidate descriptions: 1381; exact distinct candidate classes: 1325. Equality grouping uses the complete selected-vertex bit set only.

Audit JSON SHA-256: `0eef4aaf9ec6441a32904eb21270ffa3a906eee97b7cad092a0c7eb526d24be4`. Auditor SHA-256: `0f382159c8a09236e37d1fde2ed21aa86122d44b2cca3ccb21f75e1790b918a0`.

No optimizer, compiler, or software test was invoked. The audit does not resolve Hamiltonicity of any surviving candidate.
