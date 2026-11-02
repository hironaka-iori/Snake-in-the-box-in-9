# Independent final review

The checked result is one additional local count exclusion, together with its application to actual snakes and both graph orientations. I found no mathematical defect in that theorem or the reviewed numerical comparisons. The other six plain-count exclusions remain unproved. The three finite experiments preserve the previous comparison values; they do not establish a new snake bound.

This review was read-only except for this report. No Lean compiler, SAT solver, graph search or whole-graph potential iteration was run. A separate small RUP verifier was executed in memory without changing the saved evidence.

## Checked statement and proof chain

`lean/PlainCount110.lean` proves:

1. `count_pattern_refuted`: the local model for directions `012340` and exact counts `[5,5,2,4,5]` is refuted.
2. `actual_counts_excluded`: an actual six-transition snake window with that canonical direction shape cannot have those five internal counts.
3. `actual_graph_exclusion`: for every actual nine-transition window and count offset $s\leq1$, neither the forward nor reversed hit for that key can occur.

The first statement composes `D012340A55245.sat` with `D012340A55245.unsat` through `Tags.refuted_of_sat`. The semantic theorem obtains a satisfying assignment from the local axioms using the checked clause tags; the independently checked contradiction rules out such an assignment. The actual-snake statement invokes the existing coordinate-relabelling bridge. The graph statement invokes `Reference85.refuted_key_retained`, which reverses both directions and counts in the reverse case. There is no collective reference-catalogue premise in these three statements.

All five symbols are below 6, so the bounds are singleton intervals. The theorem excludes exactly the stated count tuple, rather than every tuple below its componentwise upper bounds. The hypotheses $r+6\leq m$ and $r+9\leq m$ respectively ensure that the local and graph windows fit inside the snake. The wrapper adds no mathematical definitions.

I verified all 65 successful module receipts against the current source, saved source snapshot, compiled object and log hashes. Every receipt has exit code 0 and no timeout. None of these sources contains `sorry`, `admit` or `native_decide`. The six printed axiom reports agree with `PlainCount110`'s log: the semantic Boolean check uses only `propext`; the other five statements list only `propext`, `Classical.choice` and `Quot.sound`. These are the retained successful checks, not new compilations in this review. I did not rebuild the historical dependency environment.

## Independent RUP audit

I reviewed the logic in `scripts/audit.py`. It checks the core's decoded Lean clauses against the selected clauses of the remapped full CNF, verifies the remapped CNF and LRAT hashes, and performs ordered reverse unit propagation with positive earlier-clause hints. Each derived clause must lead to contradiction when its literals are negated, and the final derived clause must be empty. This is a sufficient test for the particular RUP-only proof used here; the audit does not purport to accept arbitrary LRAT syntax.

I also replayed the same saved proof using a separate Boolean-assignment implementation. This passed with 1664 core clauses selected from 59251 full clauses, 2007 deductions and 177364 hints. The final clause was empty. The remapped proof hash is `56f4afcea5d078fcadddda1bb6c7e9b8d03694aec165dde1f9ccd29daef6922d`.

The preliminary `plain-generation.json` reports an earlier proof with 2311 deductions and 217881 hints and retains its historical pending status. The later remapped/trimmed proof, isolated plan, successful receipts and `proof-summary.json` are the final evidence. Their different counts are explained by the preparation pipeline, which takes `plain-core-s1.trim.lrat`, remaps variable and clause identifiers, and regenerates the checked modules. The earlier record should remain labelled as an earlier stage.

## Probe qualification and cycle cuts

All seven initial plain-probe records retain `UNSAT_UNCERTIFIED`. Exactly one, edge 2139224, has three dynamically added cycle cuts. The other six, including the proved case edge 3534483, have zero dynamically added cuts. I checked each of those three recorded vertex sets is nonempty, has no repeated vertex, and every vertex has at least two neighbours within the set. This is the relevant necessary-condition test used in the experiment. It is not a Lean proof of the remaining case.

Zero dynamically added cuts does not mean that the original encoding omitted acyclicity. The local `Axioms` includes acyclicity, and the generated semantic source has checked `.cut` tags for standard clauses. This is consistent with the actual-snake interpretation. The completed semantic proof checks all clauses it actually uses.

## Native graph experiments

The count-exclusion scripts apply the six-transition shape to direction positions $s+2,\ldots,s+7$ and the corresponding five counts to positions $s,\ldots,s+4$, for $s=0,1$. Their reverse tests reverse the count tuple together with the direction word. The share experiment uses only the last six directions and last five counts, as required for the five-centre share contribution. Alternative credits are combined by a maximum. The completed and conditional baseline weight hashes are checked against their pinned source models.

| Experiment | Keys remaining | Change beyond milestone 109 | Completed mean/range | Conditional mean/range |
| --- | ---: | --- | --- | --- |
|One checked count exclusion|4, 944, 051|865 additional keys removed|483 /551|496 /602|
|All seven count exclusions assumed|4, 940, 143|4773 additional keys removed|483 /551|496 /602|
|Seven additional share credits assumed|4, 944, 916|2585 edge weights increased in each profile|483 /551|496 /602|

The first row removes 2957 keys in total, including the 2092 from milestone 109. The second removes 6865 keys in total. The third retains the milestone 109 key set and raises selected credits to 76; it is a separate hypothetical experiment. The second and third rows must retain their assumption labels.

For all six saved profiles I independently checked cycle chaining, cycle weight sum divided by cycle length, survival in the saved removed-index lists where applicable, potential-file hashes and lengths, minimum potential 0, the recorded maximum potential, and the potential inequality on every listed cycle edge. I also checked both exact comparison fractions and integer parts:

$$\frac{1098960+8\cdot483+551}{4200+483}
=\frac{157625}{669},\qquad
\frac{1098960+8\cdot496+602}{4200+496}
=\frac{551765}{2348}.$$

Their integer parts are 235 and 234. The saved experiment programs additionally assert the potential inequality on every remaining edge using integer arrays. Those exhaustive inequalities were not rerun in this review; their implementation and recorded results were inspected. The saved potential ranges are verified ranges of these potentials, without a new independent proof here that no alternative potential has smaller range.

Each experiment exhibits a cycle attaining its reported mean. Together with an all-edge potential inequality, this establishes the claimed exact minimum mean for that specified finite graph and weight function. It does not transfer that experiment into a new complete Lean graph certificate. The source explicitly records this remaining gap.

## Minor reporting issue

In `count-profiles-all/results.json`, the per-rule field `additional_to_prior` is an order-dependent marginal: the script updates `drop` after each preceding rule. It therefore measures new deletions beyond milestone 109 and all earlier rules in sorted order. In particular, the proved rule contributes 795 at its position in the seven-rule experiment, while its independent contribution beyond milestone 109 is 865. The aggregate 4773 is correct. No source change was made; prose should avoid treating all per-rule values as independent comparisons with milestone 109 alone.

## Mathematical note and conclusion

I read `mathematical-note.md` at hash `a7d3e492154c2f4ad0a8323d016d9a5c9742166f7a187f0c0dc4bee11682979c`. Its exact exclusion, orientation statement, proof counts, 865 and 4773 deletion counts, cycle-cut qualification, unchanged comparisons and distinction between local proof and global prerequisites agree with the reviewed evidence. The count periods stated there match the saved all-seven experiment up to cyclic shift: completed $(2,5,6,3)$ and conditional $(4,3,5,4)$. Symbol 6 continues to mean the interval $[6,21]$.

The note's recommendation to test a condition covering a family of surviving configurations is consistent with these results. This review makes no prediction that such a condition exists or improves the bound. The remaining 1366 reference entries are unchanged by proving this additional key outside the original union.

## Final evidence pins

| Artifact | SHA 256 |
| --- | --- |
|`lean/PlainCount110.lean`|`dba23fc33bc520789452949c9a5737dddf593176a4efcec9f3b1dab5efe9db8d`|
|`data/PlainCount110-audit.json`|`cc24fb5a8e4eeb09e89144d8c861b39b3aaa3cff1112f03e712e7744d585ed3c`|
|`data/proof-summary.json`|`144a34aea7a0bae92507ae0ead814ade48a6420ea1e3dda0023c4c3ff11727d7`|
|`scripts/audit.py`|`67dd591d6d886e9f348a08fd2a184ac1999839a0d3b92ca8ab1a802f7e24f2fd`|
|`data/count-profiles-one/results.json`|`ee1cf10622a4ed166251d52c4b56271f98f54ec2a0d1ed966bfe3068ec9d7b1a`|
|`data/count-profiles-all/results.json`|`93e38e0497e8a693f5ba5ada388c9dbb807d1236b266776391b1f74c93cd0963`|
|`data/share-profiles/results.json`|`038bab10af9658d53a8c9fe3dea364d2ac1d4f43691fd49aabe900a540ef40e1`|
