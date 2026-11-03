# Milestone 122 proof receipt review

The bounded audit passed for the 58 modules in `end26-plan.json` and nine support, geometry, counting, assembly and arithmetic modules: **67 completed modules and 24 printed axiom reports**. It verified 1,332 distinct file hashes and nine additional provenance pins. No substantive proof-scope defect was found in the reviewed sources.

The audit compared each current source with its successful receipt and immutable source snapshot, verified the object, log and checker snapshot, checked every recorded dependency hash, and resolved each direct import in the recorded search-path order. Local imports resolve to the intended isolated objects. All selected sources are free of `sorry`, `admit` and `native_decide`; every printed axiom list is a subset of `propext`, `Classical.choice` and `Quot.sound`. This audit read existing evidence; it ran no compiler, solver, native refutation replay or full-graph computation.

## Mathematical scope

For a fitting window with canonical transition sequence $012032$, the concrete theorem `actual_pair26_endpoints` proves

$$
\alpha_{r+2}\le2,\quad\alpha_{r+4}\le6
\quad\Longrightarrow\quad
\operatorname{dist}(v_{r+2},e)=\operatorname{dist}(v_{r+4},e)=2
$$

for each actual endpoint $e\in\{v_0,v_m\}$. Its local contradiction has been supplied by the completed certificate; no unproved local endpoint premise remains. These are bounds on actual counts. In particular, the graph symbol $6$, which represents $[6,21]$, cannot by itself supply the hypothesis $\alpha_{r+4}\le6$.

The proof checks the 498 positive endpoint literals outside the common distance-two sphere of normalized centres $3$ and $6$. Their decoded vertices cover precisely that complement. The local semantic theorem, the checked contradiction, and the canonical-frame pullback then give the actual endpoint statement. The normalized common sphere consists of 14 vertices.

`EndpointAssembly122.actual_equality_endpoints` is checked with three explicit local endpoint premises, for count caps $(2,6)$, $(3,5)$ and $(4,4)$. The existing minimum-count theorem and reversal reduce actual equality $\alpha_{r+2}+\alpha_{r+4}=8$ to these cases. The current closed $(2,6)$ theorem supplies only one of those premises. The universal equality conclusion remains dependent on the other two completed refutations.

`EndpointFrequencyTight122.pair_window_count_le_thirteen` proves $|I|\le13$ for a finite set of fitting starts when **both** centres $r+2,r+4$ have distance two from **both** endpoints for every $r\in I$. Translation and snake injectivity place all selected positions in an intersection of two distance-two spheres, of cardinality at most 14. For nonempty $I$, the position $\max I+4$ is additional to all positions $r+2$, so $|I|+1\le14$. The empty case is handled separately. This does not establish attainability or optimality of 13.

`EndpointBudget122` supplies conditional arithmetic with $t\le13$ and explicit charge and potential inequalities. It also checks that the retained comparison slopes $2915/6$ and $496$, with nonnegative range and correction terms, cannot exclude 235 and 234 respectively. It does not assign a valid new graph credit or establish a new upper bound.

## Certificate provenance and pending work

| Count caps | Core clauses | Deductions | Hints | Exported modules | Reviewed kernel replay |
|---|---:|---:|---:|---:|---|
| $(2,6)$ | 3,886 | 2,925 | 1,045,855 | 58 | Complete |
| $(3,5)$ | 3,788 | 10,275 | 3,072,560 | 164 | Pending |
| $(4,4)$ | 3,909 | 19,349 | 3,997,908 | 214 | Pending |

All three saved full inputs have 2,216 variables and 96,117 clauses, with no added cycle cuts. Their input audit, probe pins, solver records, CNF/LRAT hashes and all 436 source-port pairs were checked. Each port differs from its generated original only by the recorded isolated import prefix. The native simulations recorded in the plans were not rerun here. The endpoint LRAT checker differs from its pinned original by its namespace, three literal-parser fuel changes from 255 to 1023, and the added axiom printouts; its soundness module has a successful receipt.

The remaining plan lists 381 modules, including both outstanding certificates and their wrappers. Three early $(3,5)$ receipts were already present when this audit finished; they are explicitly recorded as outside this frozen 67-module review. No successful `ActualEndpoint122` receipt existed at that point. A generation plan's historical `GENERATED_NOT_CHECKED` field is not used as the current status of the completed $(2,6)$ replay.

Successful `LocalEndpoint26122` and `ActualEndpoint26122` records precede a later budget elaboration error in one stopped run. The repaired budget succeeded in another run before the initial tight-count elaboration error. The final tight-count repair passed in 13.672 seconds. The audit accepts only individual successful records matching the current receipts and preserves the stopped run statuses; diagnostic `sorryAx` entries from failed attempts are not counted as successful axiom reports.

## Saved evidence

- `data/proof-review.json`: SHA256 `276553d90e6b3f2515cebc810e27587e8f0d81e913964cec0507fb9e9d71bf4e`.
- `scripts/audit_receipts.py`: SHA256 `a3efc29ec6b7288b5c66a2405771bdea486999af9dda21aa421f496450eec26b`.
- Final tight-count source: SHA256 `1613a81d27618dd4234648814965beac98f6a8c1d821d8312f880b4ee936823c`.
- Final tight-count receipt: SHA256 `aa4b66c4be773fa4ba0995d5675cb6d1df69d24b1de34c3d8077fa4ca5513895`.

The JSON contains exact per-module source, object, receipt, log, snapshot, checker and direct-import hashes. The audit script prints its result by default; `--output` requires a new output path and will not overwrite saved evidence. Graph experiments, the manuscript, earlier milestones and live proof batches were not changed.
