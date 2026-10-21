# Exact obligation boundary

Frozen six-centre source: `75404cc705135dd1f0526ecc9f1d198d3fbf0366`.
The full, exact Lean statement (including each `hw2` through `hw6`) is preserved in
`upstream/work/spectral/stronger/AggregateDirectionK6R34C7WShare231.lean`.
No ellipsis in the table below is intended as a replacement target statement.

| Proposition needed | Lean statement or exact source reference | Existing evidence | Remaining work / other branch |
|---|---|---|---|
| Count-window exclusion, all lengths 2 through 6 | Exact `hw2`, `hw3`, `hw4`, `hw5`, `hw6` binders of `upper_231_of_direction_windows_and_shares_all` in the preserved source | 15,959 exact keys match DRAT-verified records; 313 local CNFs and 202 CNF/DRUP pairs match those hashes; four shortest cores have fresh independent RUP replay, with Lean checking in progress | Generate/replay complete Lean refutations and prove packed-table coverage. `CountWindowBridge` now proves arbitrary-snake normalization, reversal and exact interval semantics at threshold 8; its refutation-family premise is still explicit. `relaxed-keller` supplies conditional aggregation, not unconditional exclusions |
| Exact two-centre table coverage | `CountWindowPairs231.hw2_of_pairs` matches the existing aggregate `hw2` premise | Kernel-checked coverage of all 64 positive truncated count pairs by four exact interval keys and their reversals; arbitrary-snake shape and count transport compiled with allowed axioms | Instantiate the four explicit refutations; three have passed, one remains in the current batch. This does not discharge `hw3` through `hw6` |
| Exact three-centre table coverage | `CountWindowTriples231.hw3_of_triples` matches the existing aggregate `hw3` premise | All 1,024 positive truncated symbol combinations across the two valid four-edge shapes covered by the exact 91 keys, with kernel-checked reversal and arbitrary-snake transport | The 91 concrete refutations remain explicit; the coverage theorem alone does not discharge `hw3` |
| Six-centre share lower bound | `∀ j, 1 ≤ j → j + 7 ≤ m → 21 ≤ windowShare p j` | 34 independently replayed CNFs; Lean Boolean and applicability batches running; case 01 passed a fresh 29-module source rebuild; canonical transport and complete 34-shape coverage now compiled | Remaining 33 concrete applicability checks, remaining Lean refutations, and final integration |
| Parallel-share geometric components | `parallelShare_frame`, `parallel_window_rev`, `Axioms.parallel_unary_weight`, `ParallelShareIdentification.share_eq_core` | Four new source modules compiled with only allowed axioms; hash-checked incremental receipt in `data/parallel-share-bridge-development.json` | Connect these components to exact CNF variable and clause tables; final full fresh rebuild still required |
| Shape coverage | Every seven-edge snake window canonically belongs to the exact 34-shape share family | `ParallelShareShapeBridge.window_shape_mem` compiled with allowed axioms, using a direct kernel check over all restricted growth strings; its shape order matches all frozen CNF records | The uniform share-family bridge is compiled; instantiate its 34 explicit refutations and identify the resulting sum with the aggregate premise |
| Share coverage multiplicity | `∑ i ∈ Finset.range (m - 7), windowShare p (i + 1) ≤ 6 * totalShare p` under `7 ≤ m` | `sum_windowShare_le`, already supplied on relaxed branch | Independent frozen source rebuild; no new mathematical proof needed |
| Global parallel-share bound | `4 * totalShare p ≤ 42 * totalEmptyAnchored p` | `SquareIncidence.totalShare_le` in `EmptyShareBound.lean`; first-stage frozen component build passed | Final integrated theorem and full fresh closure audit; no corner-share substitution |
| Aggregate with endpoints | `21 * (∑ i, localAlpha p i) + totalShare p + 735 * (m+1) ≤ 193494` under `1 ≤ m` | `weighted_identity_bound`, upstream source | Fresh build queued; endpoints each at least four are paid in the final conditional chain |
| Corner charge target, alternative route | Exact `hlower` binder of `EmptySquarePacking.upper231_of_charge`: `114*(m+1) ≤ (∑ x, selected p x * (24*(∑ ab, singleton p ab x) + shareN 12 p x)) + 1145` | Packing/loss/DP soundness supplied by main | Universal lower bound absent; frozen abstract counterexample survives currently saved constraints |
| Unconditional 231 | `theorem upper_bound_231 {m : Nat} (p : Snake m) : m ≤ 231` | No such completed theorem found in inspected current branches | Discharge all above premises internally, then freeze and rebuild full custom closure |
| Verified interval | `Nonempty (Snake 191) ∧ ∀ m, Nonempty (Snake m) → m ≤ 231` | Existing `lower_bound` witness | Combine only after unconditional upper theorem is checked |
| Seven-centre 230 | `89*m ≤ 19*A+C`, `27*(m-8) ≤ 7*S`, and `C ≤ 703` suffice | Numeric lemma compiled locally; seven-centre contributor batch still active | Verify exact state potential and boundary; finish 58,817-key set and full semantic/Lean chain |

Five evidence levels remain separate: solver UNSAT; independently replayed proof;
kernel-checked Boolean refutation; applicability to every snake; unconditional bound.
Neither a solver receipt nor a generic soundness lemma crosses all five levels.

The 237/236 closure manifests list every absent generated import explicitly.
The old contribution logs are retained, but a source file naming `upper_bound_236`
and an old 237 audit do not certify the present frozen source tree independently.
