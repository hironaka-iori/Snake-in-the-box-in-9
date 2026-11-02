# Inspection of the two remaining cycles

The most useful next count-sum test is on shapes $(0,1,2,0,3,4)$ and $(0,1,2,0,3,1)$ with middle count exactly 5 and four outer counts summing to at most 14. Both saved cycles contain the exact tuple $(4,3,5,4,3)$ on one of these shapes. A proved lower bound of 15 for this family would exclude an unsaturated window from each displayed cycle. This report establishes no satisfiability result or general inequality.

The inspection reads the saved family-profile cycles and existing direction table, decodes their counts, and compares prior local evidence. No solver or Lean compiler was run. No existing evidence was changed. It does not re-evaluate the full graph or establish that removing these cycles improves its minimum mean. Concurrent milestone 112 probes are outside this report's evidence.

## Alignment

For count code $c$, the six symbols are

$$
b_j=\left\lfloor\frac{c}{6^{5-j}}\right\rfloor\bmod6+1,
\qquad 0\le j<6.
$$

They represent actual counts at centres $r+3,\ldots,r+8$. Symbol 6 denotes $[6,21]$; smaller symbols are exact. For nine-transition word $D$, the two five-centre windows use slices $D[2:8]$, $D[3:9]$ and count slices $b[0:5]$, $b[1:6]$, respectively. The tables give the suffix window. Both offsets were decoded: each first window agrees with the previous row's suffix around the cycle, after the necessary relabelling and reversal. Thus these tables cover all windows at both eligible offsets.

Each shape is the smaller canonical representative of its forward and reversed direction words. `R` means the counts were reversed together with the directions. Ties retain the forward representation. The outer sum uses positions 1, 2, 4, and 5. When a tuple contains 6, its displayed sum is a clipped-count sum, which can be smaller than the actual sum.

## Completed-profile cycle

The 14-edge cycle has mean $3384/7$ and recorded potential range $3860/7$.

| Edge | Direction | History | Code | Shape | Orientation | Five symbols | Outer sum |
|---:|---:|---:|---:|---|---|---|---:|
|238796|35|0|27812|012034|F|$(4,3,5,4,3)$|14|
|3526061|352|4|26909|012340|F|$(3,5,4,3,6)$|17|
|1649600|173|0|21488|012034|R|$(3,6,3,4,5)$|18|
|373273|47|0|35619|012310|F|$(4,3,6,3,4)$|14|
|2612587|258|0|27094|012034|F|$(3,6,3,4,5)$|18|
|3533820|352|16|22598|012340|F|$(6,3,4,5,3)$|17|
|1651834|173|0|42279|012034|R|$(4,3,5,4,3)$|14|
|370501|47|0|20398|012310|F|$(4,5,3,4,5)$|18|
|2613031|258|0|29078|012034|F|$(5,3,4,5,3)$|16|
|3474715|351|16|34503|012034|R|$(4,3,5,4,3)$|14|
|1615881|171|22|20397|012310|F|$(4,5,3,4,4)$|17|
|231976|34|60|29072|012034|F|$(5,3,4,4,3)$|15|
|3363560|348|0|34468|012034|R|$(5,3,4,4,3)$|15|
|1608817|171|0|20187|012310|F|$(4,4,3,5,4)$|17|

Only the two `012340` suffixes are covered by milestone 111's proposed sum family. Their middle count is exactly 4, so only its unconditional outer bound 17 applies. Both attain that bound in clipped symbols. Their tuples are reversals of one another; their actual outer sums can exceed 17 because each contains symbol 6.

The other shapes receive no credit from that family. In particular, the `012034` tuple $(4,3,5,4,3)$ has middle 5 and outer sum 14 on three suffix edges. All its counts are exact. Raising only the `012340` bound would still leave the conditional cycle untouched.

## Conditional-profile cycle

The three-edge cycle has mean 496 and recorded range 602. All count symbols are exact.

| Edge | Direction | History | Code | Shape | Orientation | Five counts | Outer sum |
|---:|---:|---:|---:|---|---|---|---:|
|1131395|108|0|26908|012031|R|$(5,3,4,5,3)$|16|
|2139224|198|0|21483|012314|F|$(5,4,3,5,4)$|18|
|17417|2|0|35588|012031|F|$(4,3,5,4,3)$|14|

Direction 108's forward suffix is canonically `012302`, with counts $(3,5,4,3,5)$. Reversal produces the listed `012031` tuple. Combining the reversed shape with the forward counts would specify a different test.

No `012340` window occurs at either offset. Its outer sums, paired with middle counts $(4,3,5)$, are $(16,18,14)$. These resemble the completed cycle's low-sum windows, but existing shape-specific bounds do not transfer to them without proof.

## Earlier evidence and counterexample check

Milestone 110 already tested the exact `012031` tuple $(4,3,5,4,3)$ in `data/plain-probes/edge17417-plain.json`: native `UNSAT_UNCERTIFIED`, with zero added cycle clauses. The tuple $(5,3,4,5,3)$ has the same status in `edge1131395-plain.json`. The `012314` tuple was also tested, with three cycle cuts. None supplies a broader count-sum theorem or the missing actual-snake proof.

The older `012034` plain probes concern $(4,5,5,2,4)$ and $(5,5,4,2,5)$, rather than the common target. The inspected milestone 72 probe directory contains no matching positive selected-set witness for either target shape.

A bounded scan of positive selected-set records in milestones 72, 73, 97, 110, and 111 found no direct local-witness counterexample to this two-shape test. This is a limited evidence search. The principal nearby records have different scopes:

- Milestone 72's `w002-None.json` is a positive local witness for `012345`, with symbols $(2,6,2,3,6)$.
- Its `general3-cap15-certificate.json` is a positive relaxation for `012301`. Its cyclic control has counts $(1,1,1,1,1)$ and explicit cycles. Neither refutes an acyclic restriction on the target shapes.
- Milestone 111's four checked local forests all have shape `012340`, with counts $(9,3,8,2,3)$, $(11,3,2,6,12)$, $(11,4,2,4,9)$, and $(12,4,2,5,9)$. None has the target shape or middle count 5. The first still precludes an unconditional outer bound 18 in that older local model.
- Milestone 97's saved witness tests are abstract graph walks, which do not by themselves falsify an actual-snake inequality.

Local acyclicity must remain in the next test. Any added cycle clauses must retain their semantic justification in subsequent certificates.

## One bounded next test

Continue the count-sum route by extending its shape dependence. Test two cells, with canonical words `012034` and `012031`, respectively, and

$$
\alpha_{r+3}=5,
\qquad
\alpha_{r+1}+\alpha_{r+2}+\alpha_{r+4}+\alpha_{r+5}\le14.
$$

Use existing radius-four geometry, outer individual bounds $[0,21]$, and the sorted concatenation of four corner-literal lists, retaining repeated occurrences. Keep the endpoint and acyclicity conditions. A fixed modest time limit per cell gives a bounded falsification test. Independently verify any positive selected set before using it as a local counterexample; a timeout remains unresolved.

If both cells are refuted and their certificates and count semantics are checked, they give

$$
\alpha_{r+3}=5
\quad\Longrightarrow\quad
\alpha_{r+1}+\alpha_{r+2}+\alpha_{r+4}+\alpha_{r+5}\ge15
$$

for these two shapes and their reversals. The equality is deliberate: replacing it with $\alpha_{r+3}\le5$ is stronger and requires another check. This proposed family would exclude the common exact tuple on three suffix positions of the completed cycle and one of the conditional cycle. It would not establish a larger graph minimum mean or an improved integer bound without further graph and charge verification.

## Evidence pins

| Source relative to repository | SHA-256 |
|---|---|
|`milestones/111-critical-count-intervals/data/family-profiles/results.json`|`1574a0780b6513b3edb63118bbb609464ae6741023a0792bfe57e38f7cc9ba77`|
|`milestones/59-extended-share-window/extended/data/model.json`|`2334325d650cc9b71c0c6ab836183cecd4f1fc4d8b6555f63211592a22a0e2bf`|
|`milestones/110-critical-cycle-core-screen/data/plain-probes/edge17417-plain.json`|`bb58ed0c4dd3434aa7e1b1829e5f6595330c773fc514ae82472dd5429d267755`|
|`milestones/72-four-count-proof-closure/critical-current/data/probes/w002-None.json`|`700b48ed3a1de06d31111972108dcaccb186a6c9c3337e53ab98134e14c3ee2f`|
|`milestones/111-critical-count-intervals/data/witness-audit.json`|`9056123bf929d60bcca1f2b6c0fd25e63d18451d7980c147d871628d689e78b8`|
