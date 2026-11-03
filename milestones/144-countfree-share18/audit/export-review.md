# Bounded review of the share18 Lean export

Status: `PASS_BOUNDED_EXPORT_SOURCE_AND_TRANSPORT_REVIEW_LEAN_PENDING`.

No source, semantic-metadata or certificate-transport discrepancy was found. The fixed Lean replay can continue. The actual share18 conclusion still requires successful checks of the complete dependency chain and its final theorem statements.

The export contains 1,324 Lean modules, including 104 semantic shards and 604 proof-check modules covering 2,416 replay segments. All generated source hashes match the plan. The recorded module order respects every local import, and the final reversal module reaches all 1,324 modules. External imported objects resolve under the driver's declared search order; their paths and hashes are saved in the review receipt. Their transitive correspondence to source remains inherited from the existing environment evidence.

The audited scalar parameters are cap 17, resolution 12, five count intervals `[0,21]`, and window `[0,1,3,7,6,14,30]`. The export retains the explicit original IDs of all 13,224 core clauses. It replaces these input IDs by the consecutive IDs 1 through 13,224 only in the compact proof. Original derived clause IDs remain unchanged.

The variable map is a bijection on the 6,371 needed semantic variables. The 5,779 variables appearing in the core or proof come first; the remaining variables supply semantic counter and totalizer inputs. The compact CNF, every generated raw core clause, both packed semantic leaf streams, all tags, and every counter and totalizer table were independently checked against the already audited original data. The semantic leaf streams preserve the different meanings of primary selections, endpoint flags, registers, empty squares and share thresholds. Repeated incidences remain present.

A streamed comparison checked all 145,215 transported deductions and all 14,710,881 hint occurrences. Literal signs, order and multiplicities are preserved. Hints to original clauses follow the explicit original-ID map; hints to derived clauses retain their original IDs. The saved proof-variable set was reconstructed from these lines and matched exactly. This was a transport comparison, with no new unit-propagation replay.

The checker offset is 8,192. All 5,779 active variables lie below it; the largest possible negated-literal word is 13,972. The 14-bit words also accommodate all 14,114 recorded slots. The generated base and fast checker sources match the inspected constant-and-namespace transformations. Proof data use Lean `Nat`, with signed CNF clauses represented as `Int`; no machine-integer truncation is introduced by these source types.

The forward wrapper states that for any `Snake m`, any fitting six-transition window with word

\[
(a,b,c,a,d,e),
\]

and five distinct coordinate indices below nine,

\[
18\leq\sum_{i=0}^{4}\operatorname{coreShare}_{12}(p,r+i+1).
\]

The fitting assumption is \(r+6\leq m\). The reverse wrapper asserts the same conclusion for \((e,d,a,c,b,a)\), using the reversed snake at index \(m-r-6\). Both statements have no parity or extra singleton-count assumptions. The forward proof uses the ordinary universal bound on singleton-square counts; the reverse proof transports the same five-centre sum through `coreShare_window_rev`. The bridge requires the cap to be exceeded, so cap 17 gives the intended lower bound 18.

The exporter reports a successful packed-proof simulation, including checkpoints. Its implementation and pinned result were inspected, but this audit did not repeat that simulation or decode the large packed LRAT arrays. Those arrays were hashed. The original Boolean refutation was independently replayed in the preceding alternative-certificate review; that result does not replace Lean checking of the exported representation.

The remaining gate is successful Lean checking of every semantic shard, structural check, proof-check module and final contradiction assembly, followed by `Share144.Refuted`, `Share144.Geometry` and `Share144.Reversal`. Final source, object, dependency and log hashes must match, and the printed final theorem axioms must be restricted to the standard permitted set. A successful warm-up or initial prefix alone does not establish the share18 theorem. No global snake bound follows from this export review.

No Lean compiler, solver, graph search, proof generator or propagation replay was invoked. Exact source maps and the independently checked facts are recorded in `data/export-review.json`.
