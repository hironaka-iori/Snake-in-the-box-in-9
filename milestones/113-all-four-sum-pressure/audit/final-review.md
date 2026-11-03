# Independent bounded review of milestone113

The direct witness and saved-cycle checks passed. No defect was found within the inspected scope. The concrete pair-count contradiction remains unproved: both proof-producing native runs timed out. No new global upper bound follows from these experiments.

Reproducible checks are in `scripts/independent_check.py` and `data/independent-check.json`. The script launches neither a solver nor Lean. By default it prints results; `--output` creates a new file exclusively. Supplemental read-only checks covered the budget receipt and interval-cycle avoidance. The reviewer authored the geometric helper earlier, so its receipt/source inspection is not an independent authorship review.

## Local witnesses

The checks reconstructed the 421-vertex radius-four region around the internal centres of $[0,1,3,7,6,14,30]$. They verified window inclusion, induced degree at most two, positive interior selected degree, at most two interior endpoints, acyclic components, all 12,996 explicit square/six-cycle clauses and every additional saved cycle cut. Counts were computed directly with multiplicities and checked against all interval and sum conditions.

| Probe | Selected vertices | Exact counts | Components | Interior endpoints |
|---|---:|---|---|---|
|`middle445`|168|$(10,4,4,3,6)$|30 components; complete sizes in JSON|$130$|
|`upper55455`|113|$(5,5,4,5,5)$|$39,35,20,19$|$34,37$|
|`middle545-pair9`|109|$(6,5,4,5,3)$|$38,35,31,5$|$34,69$|

The last witness has pair sum exactly $9$ and central counts $5,4,5$. It prevents raising the proposed local threshold to $10$ under these same assumptions. It does not establish the lower bound $9$. These disconnected forests have relaxed boundary conditions and are not complete snakes.

## Evaluators and budget

Both evaluators use directions $D[s+2:s+8]$ and counts $b[s:s+5]$ for $s=0,1$. Symbol $6$ represents $[6,21]$. The eight pair-evaluator rules have reversal-symmetric bound vectors and position sets; the interval evaluator reverses both directions and counts explicitly. Deletion is tested at both placements. A positive deficit deletes a key only when all summed symbols are below $6$. Only suffixes receive excess credit, combined by maximum.

`PairBudget113` passed three audits in 15.266 seconds. Source, snapshot, object, log and direct dependency hashes match. The pair deficit is bounded by its two excesses; its maximum with the prior credit uses the same $4a+b\le120$ capacity through `SumBudget112.weighted_window_budget`. The local lower bound remains a hypothesis. Separate full budgets or addition of all competing credits are not justified.

## Cycles and finite comparisons

All four recorded profile cycles passed checks of full direction/history/count keys, endpoints, chaining, retained membership, baseline weights, zero bonuses, means, potential hashes/ranges, cycle potential inequalities and exact comparisons. Interval cycles also avoid the interval rule at both placements and orientations. Full-edge scans were inspected and pinned rather than repeated.

| Experiment | Remaining keys | Removed beyond 112 | Completed mean/range | Conditional mean/range |
|---|---:|---:|---|---|
|Interval45454|4,887,350|21,877|$484/557$|$496/602$|
|Pair24|4,867,866|41,361|$484/557$|$496/602$|

The exact comparisons remain $1103389/4684$ and $551765/2348$, with integer parts $235$ and $234$. Both experiments assume unproved restrictions, including in the profile named `completed`.

Pair24's completed nine-cycle has weights $720,360,492,600,360,372,600,480,372$, summing to 4356. Its conditional four-cycle has weights $616,618,252,498$, summing to 1984. Every applicable suffix deficit under each of the eight rules is zero. These cycles survive coefficient-independent deletion and retain means $484$ and $496$ for arbitrary nonnegative deficit coefficients. Balanced $24$ native potentials attain these ceilings. The full decoded windows and individual rule tests are saved in the independent JSON.

The conditional cycle's $012034$ tuples are $(5,5,4,2,5)$ at reversed edge 1820578 and $(4,5,5,2,4)$ at forward edge 4449560. They already have zero-cut native UNSAT records in milestone 110, respectively `edge1650991-plain.json` and `edge2610423-plain.json`. Neither record supplies a checked contradiction.

The precise common next target is $012310$: completed edges 1613032 and 1625348 have $(3,4,5,3,3)$ and $(3,3,5,4,3)$; conditional edge 734789 has $(2,4,5,5,2)$. All sum to $18$. Testing total at most18 without extra caps is a bounded next task for 114. A valid lower bound $19$ would remove an edge from each saved pair24 cycle; other attaining cycles could still preserve the optimum. No new probe was run here.

## Proof status and review limits

`PairGeometry113.actual_pair_sum` still explicitly assumes `hlocal`, the local contradiction under central caps $5,4,5$ and pair sum at most $8$. Source, snapshot, object and log hashes match. The geometry and budget helpers have four printed reports using only standard axioms `propext`, `Classical.choice` and `Quot.sound`.

Both proof-producing attempts used the same pinned CNF and timed out at 30 seconds: 30.110 seconds ordinarily and 30.047 seconds with `--plain`. Their partial LRAT files have 34,676,736 and 29,310,976 bytes; hashes match the saved records. These preserved partial files are not completed certificates.

Both gzip archives were independently decompressed and match the original partial-proof hashes. The final mathematical note, including its 114 next-test paragraph, agrees with the reviewed evidence. The consolidated root summary was inspected and pinned. No solver, Lean compiler or full graph scan was run in this audit. Historical dependencies were reused. Concrete pair refutation, actual-snake graph restrictions and full global integration remain outstanding. The maintained historical global bound was not re-proved here.

## Evidence pins

The following SHA256 values pin the reviewed files. The independent JSON remains unchanged.

| Artifact | SHA256 |
|---|---|
|`scripts/independent_check.py`|`898b6693449341ff828a7e217c36ffc7b201e981ccd94d01ac298182ccf09df7`|
|`data/independent-check.json`|`717b8d520e7f90e5001d42ca8f862aa0e609da21e7ccf39863d9e54ac1644f2f`|
|`data/pair24/results.json`|`0bdd988a2c7bf544d83af323685fe73e9bf48119adc70bf7bf1a7cbbe4d33a70`|
|`data/interval45454/results.json`|`0d11ddeb7a9f146f637f4cc96597614dacc1446698cfbf0fe5068a7919d3b339`|
|`data/pair-rules.json`|`eb5151118d4d22684fb52e13b05db2cab03db76727f99b3175fd8f6777f7e129`|
|`data/PairGeometry113-audit.json`|`4f9693eea6ee0b5c444bea836fe9118db7f6ced8c8a9b5912a6f1c33aab12a22`|
|`data/PairBudget113-audit.json`|`cc72af732c689b51e332ea201e35683dd096a697493b3bb04dae5aaa51df4423`|
|`data/012034-middle545-pair8-solver.json`|`fcc961b63a9a2d810e316e74ed8b4815defc82883a42fe2550a84018b26434db`|
|`data/012034-middle545-pair8-plain-solver.json`|`69b0e872d88b0be18e36c89806b5e336c11b55385d60f08ce3b9b6c0f93b886b`|
|`mathematical-note.md`|`94698c643e27e9dbbcdab46775a24cb42dfd5168aefd0e615afd7bd1a9e99bfc`|
|`data/proof-summary.json`|`10be0a897fc90f35f101f80bf919dca21f216b4e38cc67ff13f755e9d5daec29`|
|`data/large-artifact-archives.json`|`11b250b13829120e46070a222c2b0a21de2d4a86ab7aa3bd2ba396334d61e2dd`|
