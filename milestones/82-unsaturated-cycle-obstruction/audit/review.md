# Independent review of the unsaturated cycle obstruction

Reviewed 2 November 2026. The obstruction is correct for the fixed finite graph and the stated class of edge-weight increases. It limits that comparison method under its unchanged boundary budget. It does not establish that the four-edge cycle is realizable by a snake or rule out stronger geometric, reachability, boundary, or state-space arguments.

## Verified current evidence

The current source/object/log hashes match `data/lean-audit.json`, whose status is `PASS_UNSATURATED_OBSTRUCTION_ARITHMETIC`, exit code zero. All six printed audits use no axioms beyond `propext`, `Classical.choice`, and `Quot.sound`; the literal count and weight checks use none. The linked graph-audit hash matches, and all five input-source fingerprints in that graph receipt match current files.

The reviewer independently decoded all four six-count codes, compared their rows with the generated Lean `cycleCounts` literal, checked the ordered weights, verified closed cycle incidence, and recomputed the budget arithmetic. No compiler run or full all-edge replay was started by this review.

| Edge index | Six-count row | Weight |
|---:|---|---:|
| 372796 | (5,2,4,5,5,2) | 252 |
| 2610423 | (2,4,5,5,2,4) | 480 |
| 3534483 | (4,5,5,2,4,5) | 600 |
| 1650991 | (5,5,2,4,5,5) | 600 |

Every digit is strictly below six. The recorded endpoints form a closed four-edge cycle, and its total weight1932 gives mean483.

## Finite graph certificate

`check_graph.py` reads the current proof-supported model, requires its additional-share-assumption list to be empty, and verifies the referenced local-audit hashes. It loads the saved source graph and checks every recorded raw array hash. It then reconstructs the count-free-floor weight increases by taking maxima, compares the resulting weight hash, reads and hashes the saved potential, and checks all 4,947,008 inequalities

\[
483+\pi(v)\le w(u,v)+\pi(u).
\]

It also checks the potential range551, each selected cycle edge's actual endpoints/weight, and each selected code's unsaturated digits. The hashes and source inspection therefore support the saved result as an exact certificate for this finite graph. This bounded review inspected that procedure and receipt; it did not repeat all 4,947,008 inequalities independently.

Summing the potential inequalities over any closed walk cancels the potential terms and gives mean at least483. The displayed cycle gives mean at most483, so the graph's minimum cycle mean is exactly483. This argument does not depend on the numerical minimum-mean search algorithm once the cycle and potential certificate are supplied.

## Nonnegative bonuses

Let b(e) be an edge bonus on the same graph. Assume b(e)>=0 for every edge and b(e)=0 whenever all six recorded count symbols of e are below six. Then the old potential remains valid after replacing w(e) by w(e)+b(e). The four displayed cycle edges retain their original weights, so they still attain483. Consequently the modified graph's minimum cycle mean remains exactly483.

Both hypotheses matter. An arbitrary positive bonus on these unsaturated edges can change their mean. Deleting an edge, changing the states or admissible transitions, restricting reachability, or introducing a different boundary inequality is outside the conclusion. A correction based on information outside the six recorded counts is covered only if it also satisfies the stated vanishing condition.

The Lean source checks the local nonnegative-bonus potential implication over rational numbers, along with the cycle and budget arithmetic. The graph-wide minimum-mean conclusion is obtained by combining these facts with the separately checked finite arrays and the elementary cycle-summation argument. The source does not contain a single theorem ingesting all saved arrays and quantifying over every graph bonus. Descriptions should retain this distinction.

## Budget limitation

The unchanged comparison budget and a slope/potential certificate yield

\[
(p+4200d)m\le1098960d+8p+R.
\]

For positive scale d, excluding m=235 through this inequality requires

\[
227p>111960d+R.
\]

Summing any four valid potential inequalities on the unchanged displayed cycle gives p<=483d. For d>=0 and R>=0,

\[
111960d+R-227p\ge2319d+R\ge0.
\]

Thus the strict criterion cannot hold. `cycle_slope`, `no_234_criterion`, and `cycle_prevents_234` check precisely these rational implications. The weaker assumption d>=0 is harmless in those statements; an actual positive scaling denominator meets it.

Even the optimistic substitution R=0 at slope483 gives

\[
m\le\frac{1098960+8\cdot483}{4200+483}
 =\frac{367608}{1561}>235.
\]

This substitution does not assert existence of a zero-range potential. It shows that reducing the potential range alone cannot make this slope exclude235 under the same budget. The statement concerns this proof criterion, rather than all possible upper-bound arguments.

## Source-generation observation

The current Lean weight literals are (252,480,600,600), and they independently match the four graph-audit rows in that order. `check_graph.py` generates the count literal from the actual rows, while its weight theorem and four potential hypotheses are hard-coded. At initial inspection, the generator checked only the four-edge total1932, rather than asserting this ordered weight list. The parent was advised to assert the ordered weights or generate them dynamically. There is no current mismatch; the recommendation guards against a future chosen cycle with the same total and different individual weights.

## Review conclusion

No current mathematical or data-correspondence error was found. The result identifies a specific obstruction to bonuses that vanish on all six-count-unsaturated edges in the present comparison graph. It supports redirecting that restricted improvement attempt. It supplies neither a new global bound nor a claim that any extremal snake follows this cycle, and makes no novelty claim.


## Final delta verification and target sensitivity

The weight-generation recommendation is resolved. The current graph checker explicitly asserts the ordered list `[252,480,600,600]` before producing the Lean source. The refreshed graph receipt passes, and the final successful Lean receipt links to its exact current hash. Current source, object, and successful-log hashes were checked again, with six theorem audits retained.

The compiler now writes a uniquely named temporary object and replaces the saved object only after compilation succeeds. The earlier object-overwrite failure remains separately recorded as `logs/UnsaturatedCycle-overwrite-failure.log`; it is distinct from the final successful log and receipt. No compiler or graph check was rerun by this reviewer.

The new `target_cycle.py` was read and its small four-row calculation checked independently. Each row's last six directions was canonicalized in both orientations and matched to the required-share catalogue. Case7302, shape012034 and proposed floor20, occurs on two edges; case7307, shape012340 and proposed floor16, occurs on one edge. Both remain among the five pending cases in the current integration receipt. The existing case7305 edge already has its required credit12.

Taking the maximum of the existing edge weight and the proposed count-plus-credit weight gives

\[
(252,480,600,600)\longmapsto(252,500,616,620).
\]

The hypothetical total rises from1932 to1988, an increase56, so this one cycle's mean rises from483 to497. The target-sensitivity input hashes match the current script, graph receipt, and required-share catalogue.

The README correctly labels this calculation conditional and specific to the displayed witness. It does not infer a whole-graph mean497, discharge either pending floor, or establish234. Other cycles can become or remain limiting. The nonnegative-bonus obstruction continues to require its stated vanishing property; additional information only evades that obstruction when it changes an assumption such as the edge set, the boundary budget, or that vanishing property.

Current receipt fingerprints:

- `data/graph-audit.json`: `d3f9fe247eabddfe7b6950ee4ebc7f897560fb411a5a3fdae811b6aa54faac1d`.
- `data/lean-audit.json`: `45737039c773fbb5ead26ef749e91b370880415f1754062a924dde6a738a5c6b`.
- `data/target-sensitivity.json`: `7405e7353cd16ec83126c59d4100642381a915b2fa322fd69cf4b090c35515b1`.

No outstanding defect remains from this bounded review.
