# Independent review of milestone 112

Status: completed against the stable mathematical note and consolidated proof summary identified below. This review used read-only Python calculations and source inspection. It launched no Lean compiler or SAT solver and changed no existing evidence. The reviewer previously wrote the generic budget, counter-semantics and geometric-transfer helpers; the concrete certificate, exporter and graph experiments were independently prepared by the parent agent.

## Exact local certificate

The full CNF was independently reconstructed from the saved tagged encoder, the window

$$[0,1,3,7,15,13,29],$$

and internal count bounds

$$[(0,21),(0,21),(0,2),(0,21),(0,21)].$$

The six transition directions are $012314$. The additional counter sums the absent corners at internal positions $1,2,4,5$, with upper bound $18$. Its four centres are $(1,0,1)$, $(3,1,2)$, $(15,3,1)$ and $(13,1,4)$. Each contributes $21$ corner occurrences. The concatenation therefore has $84$ occurrences and $70$ distinct literals. Repeated vertices remain repeated counter inputs; replacing this list by a set would change the claim. Sorting preserves the required multiplicity. The saved probe uses no cycle cuts.

The reconstructed bytes equal `work/012314-upper2-outer18/full.cnf`: $55,177$ clauses and $2,793$ variables. An independent variable-to-Boolean unit-propagation implementation replayed the original trimmed proof from precisely the recorded $3,577$ input clauses. All $5,061$ deductions and $610,721$ positive hints passed, ending in the empty clause. The verifier checked increasing derived IDs, earlier positive hint IDs, clause falsification, each hinted unit or conflict step, and the final contradiction.

The selected refinement uses $3,306$ input clauses, $7,020$ deductions and $367,588$ hints. The permutation in `data/sum-renumbering.json` is a bijection on all $2,793$ variables. Exactly $1,718$ variables occur in the selected input clauses or derived clauses; their images are exactly $1,\ldots,1718$. Both polarities transform consistently. Every remapped input clause, derived clause and hint ID was compared with the selected original refinement. Input proof IDs map back to their original full-CNF IDs; derived IDs remain disjoint and ordered. The remapped full CNF and LRAT agree exactly with these transformations.

The independent replay of `work/sum314-refined/sum3142.lrat` also passed all $7,020$ deductions and $367,588$ hints. Decoding the generated Lean `raw` list recovers exactly the $3,306$ remapped input clauses. All $36$ generated-to-isolated source pairs match the hashes in `sum-plan.json`; their only changes are the recorded import-prefix replacements. The earlier exporter failure at offset $2400$ is preserved in `preparation-attempt.json`. It is an unsuccessful export, not evidence against the local inequality. The active-variable permutation addresses its literal-width precondition without altering the Boolean problem.

## Semantic and actual-snake scope

`Sum3142.check` checks all tagged clauses, the ordinary counter metadata, base validity and negative-primary status of every extra-counter literal, and a permutation of the mapped literal list with the concatenated corner lists. `Sum3142.sat` then uses the checked append-counter adapter under the explicit outer-sum premise. The extra counter's metadata label is `.ends`, but its numerical bound is justified by the supplied sum premise through the generic adapter; it is not inferred from an endpoint bound. The ordinary counters are checked separately. This distinction is sound in the inspected proof.

The geometric transfer keeps the canonical coordinate permutation and exact corner counts. For a genuine snake $p$, a fitting start $r$ with $r+6\le m$, canonical transition word $012314$, and $\alpha_{r+3}\le2$, the proposed final composition concludes

$$\alpha_{r+1}+\alpha_{r+2}+\alpha_{r+4}+\alpha_{r+5}\ge19.$$

The source `ActualSum112.local_refuted` composes the concrete semantic satisfiability theorem with the concrete contradiction for the same CNF. `ActualSum112.actual_outer_sum` discharges the geometric transfer's sole local-refutation argument with that result. No catalogue-refutation hypothesis occurs in this composition. The final contradiction and composition have now passed Lean. All $37$ concrete/composition receipts were checked against their current source, exact source snapshot, object and log hashes. Together with the three generic helper modules, this gives $40$ successful modules and $20$ printed axiom reports; repeated printed theorem names are included in that report count. The contradiction module took approximately $1.438$ seconds and the final actual-snake/arithmetic module $15.359$ seconds in the saved runs.

This is one local count-sum result. It does not establish all inequalities used in the numerical experiments, a reversed numeric guard, a revised retained graph, or a new global snake bound.

## Shared excess budget

The inspected generic arithmetic retains the local lower bounds as hypotheses. With $x_i=\min(\alpha_i,6)$ and $\delta_i=\alpha_i-x_i$, coefficients $a,b\ge0$ satisfy $4a+b\le120$. An outer-four deficit $D_4$ and total-five deficit $D_5$ can receive the single credit

$$\max\{aD_4,\min(a,b)D_5\}.$$

It is bounded by $a$ times the four outer excesses plus $b$ times the middle excess. Across suffix centres $r+4,\ldots,r+8$, the shifted-sum argument bounds all such credits by $120\sum_i\delta_i$. The credit uses a maximum across competing rules. Adding every applicable rule's credit would exceed the proved accounting. The boundary lemma retains its endpoint, positivity and adjacent-count hypotheses.

The graph evaluator follows this convention: it tests both fitting placements for deletion, awards excess credit only on the suffix placement, and takes the maximum over applicable rules. All selected position sets are reversal symmetric, as is the middle condition, so canonical reversal does not change the tested sum. Applicability treats symbol $6$ as the full interval $[6,21]$. A positive deficit deletes a key only when every summed symbol is below $6$; otherwise it can justify conditional excess credit. These alignments match the budget's scope.

## Numerical graph comparisons

Source hashes in all three result files were checked. For each saved cycle, the original full direction/history/count key and both endpoint IDs were checked against the pinned source graph. The cycle chain, retained-edge membership, rule applicability, exact baseline weight, maximum deficit credit, cycle mean and rational comparison were independently recomputed. Every saved potential was decompressed and checked for its hash, state count, minimum zero, maximum and inequalities on the displayed cycle. The full-edge potential scans were not repeated; those remain the recorded native checks of the inspected evaluator.

| Experiment | Retained edges | Completed mean | Completed scaled range | Completed comparison | Conditional mean/range | Conditional comparison |
|---|---:|---:|---:|---|---|---|
| $a=b=24$, original six rules | 4,909,953 | $484$ | $557$ | $1103389/4684$, integer part $235$ | $496$, $602$ | $551765/2348$, integer part $234$ |
| $a=30,b=0$, original six rules | 4,909,953 | $1935/4$ | $2222$ at scale $4$ | $4413542/18735$, integer part $235$ | $496$, $602$ | $551765/2348$, integer part $234$ |
| $a=b=24$, expanded seven rules | 4,909,227 | $484$ | $557$ | $1103389/4684$, integer part $235$ | $496$, $602$ | $551765/2348$, integer part $234$ |

The expanded experiment removes $726$ further keys beyond the original six-rule experiment. Its completed cycle is the same six-edge cycle with count code $27993$, meaning all six symbols equal $4$. Its conditional cycle is the four-edge cycle also saved in the $a=30,b=0$ experiment. The original $a=b=24$ conditional result instead records a five-edge attaining cycle. All six displayed cycles have zero awarded bonus on every edge, although their survival under all rules was checked.

For the fixed original six-rule family, all $31$ integer coefficient rows with $a=0,\ldots,30$ and $b=120-4a$ recompute to the saved cycle upper bounds. The best completed-cycle upper bound is $484$, achieved as an upper bound for $a=2,\ldots,29$; the conditional upper bound is $496$ throughout. This bounds the attainable minimum mean for that fixed graph and rule family. It does not optimize potential range, establish an attained lower bound for every coefficient pair, or cover additional inequalities. Saturating $b$ is valid for this screening because the credit is monotone in $b$ at fixed $a$.

The expanded seven-rule family has a stronger coefficient-independent ceiling. On its completed six-cycle, four suffixes match the total-$20$ rule at equality and the other two match no applicable rule. On its conditional four-cycle, edges $1817939$ and $4453322$ match that total rule at equality, and edges $734051$ and $3409325$ match no applicable rule. Direct recomputation gives zero for every applicable deficit. Consequently these same retained cycles have mean $484$ and $496$ for every nonnegative choice of deficit coefficients, including noninteger choices. The balanced-$24$ native potentials attain these ceilings. Further coefficient adjustment within this fixed family cannot improve either minimum mean.

The two additional statements in `ActualSum112` express the associated comparison obstruction at any natural scale: $p\le484d$ implies $(4200d+p)235\le1098960d+8p+R$, and $p\le496d$ implies $(4200d+p)234\le1098960d+8p+R$, for $R\ge0$. Their arithmetic direction and constants were checked independently, and both statements passed Lean in the final module. These statements show that even a smaller nonnegative potential range would not make the stated comparison exclude those target values at the current slope ceilings.

The profile labels distinguish two existing baseline weight models. Even the profile named `completed` still depends here on unproved sum rules. The conditional profile additionally uses the stronger floor-$18$ assumptions. Neither numerical comparison is a newly completed unconditional upper-bound theorem.

## Local witnesses and unsuccessful probes

All six saved positive local witnesses were independently checked against their pinned vertex lists. The checks reconstructed the radius-four region and selected induced graph, verified window inclusion, degree at most two, nonzero degree at interior selected vertices, at most two interior endpoints, acyclic components, exact corner counts with multiplicities, all interval bounds and the tested sum. Their count vectors are

$$[8,3,3,3,3],\ [7,2,4,3,4],\ [4,5,3,4,4],\ [3,6,4,4,3],\ [3,3,4,6,5],\ [3,3,3,7,5].$$

They are local models with multiple components and relaxed boundary conditions. They show that the corresponding stronger inequalities cannot follow from the tested local constraints alone. They do not provide complete snakes or refute stronger global claims. UNKNOWN probes, including the $012031$ total-$19$ run with fifteen added cycle cuts, remain unresolved. The zero-cut native UNSAT probes other than the certified $012314$ case retain their uncertified status.

## Evidence pins and review limits

SHA256 values independently checked during this review:

| Evidence | SHA256 |
|---|---|
| Original full CNF | `a59166dbc6c7e24a58535c4ecf4545a1e19313e9e77c73df0b15e9ca868e317d` |
| Original trimmed LRAT | `d7a9774b9799dab40e2af9082fe07001cd45a6b31d34f37a76e956e392ebdf83` |
| Active-variable permutation | `d086312d0f3dbf61563c80717fdf6bd6133573f519fdb0930e86ce873500f711` |
| Remapped full CNF | `073691c34dfc00fe4e95390efe53bb3735dbb4b7a7d0abdd08ee38dd0fdbe1e3` |
| Remapped LRAT | `7f5ca1844ae6abd102340dee337486ed8cb5adfa6535592c5a87b429907c2009` |
| Semantic module receipt | `d739f7878f89ccfae93157e1f063c3503ef5ee59410b0d3e4462efc485899d6c` |
| Final contradiction receipt | `acbfc7b068b6722a5070652c1c9f5ebe5fb6c481255fe53edfe9083d075ce816` |
| Actual-snake/arithmetic receipt | `4990e50e3d41fbde8e2c1b9e92fb11d7b0ec33f3d3f1b603e25c02ced67a7866` |
| Actual-snake/arithmetic source | `9e5f7db4a74440971e5bd3d9ada06c1973c021614df22e94d09aa803d83f759d` |
| Complete generated-module plan | `6e6ddeae897ab8a0c1362aee41b4332163a27ca16f8402fa0eeb78d59299c901` |
| Original $24,24$ profile | `037271d1e9c8a50d5df06da7fbc153609a7a42680166802158848baf2caffbc4` |
| Original $30,0$ profile | `97a1699ef60eb6aad1bf0bd9cfe6c51b12b4e2ae1144aff299bb5d7cf2a9ef91` |
| Expanded $24,24$ profile | `b43006b67b1faea4b0c0c93cabe156641d4857ae1836aab81259519c695508d5` |
| Coefficient screen | `484efaa215d8fea2db70bc4749811651d98a2541fe7802d1378495de6db72ce7` |
| Six-witness audit | `2a4185f2c415da8e2f58ad0b668e3269068f801912d172d60b0462e64455d64b` |
| Consolidated proof summary | `0e944d1e59603610864b72f21371db1317be1862c76a2bb830804a99a751586a` |
| Stable mathematical note | `6cd200a71ac18e448392dd0793f7485090fb6af64a57b7897fd69d68acd95b07` |

All $40$ receipt hashes in the consolidated summary match the saved files. The inspected source files contain no `sorry`, `admit` or `native_decide`; all $20$ printed reports use only subsets of `propext`, `Classical.choice` and `Quot.sound`. Source snapshots, objects and logs were checked for both the concrete batch and the three generic helpers. The stable mathematical note includes the corrected historical cycle lengths and completed compilation status. Its local theorem, multiplicity discussion, budget, conditional graph comparisons and fixed-family ceiling agree with the reviewed evidence.

No unresolved defect was found within this bounded scope. Historical dependency objects were reused; this review does not independently rebuild their entire proof closure. The full-edge native potential scans were inspected and pinned rather than repeated. Graph-oriented guard proofs, the other six proposed sum inequalities, the complete revised graph certificate and the corresponding global actual-snake integration remain uncompleted. The note's wider repository status and maintained historical upper bound were not independently re-proved in this audit. No improvement to the global numerical snake bound is claimed.
