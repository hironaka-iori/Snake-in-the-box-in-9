# One-unit sensitivity of the five unfinished share floors

The floor for direction shape012034 can be weakened from20 to19 while retaining the finite graph certificate for conditional234. The other four tested one-unit reductions are obstructed for every constant slope and global potential range under the current boundary budget. All five tests are decisive.

These are computational results on the same pinned4,947,008-edge graph with1,601,856 raw states. Each test lowers only its specified floor, keeping all other full-profile floors and previous credits fixed. No local geometric theorem, arbitrary-snake graph coverage or new global bound is proved here.

## Results

| Pending case | Shape | Floor change | Exact result |
| --- | --- | --- | --- |
|7301|012032|16 to15|Obstruction:69-edge walk, weight33592, deficit632|
|7302|012034|20 to19|Sufficient potential: slope496, range601, strict margin31|
|7303|012301|16 to15|Obstruction:94-edge walk, weight45992, deficit632|
|7307|012340|16 to15|Obstruction:77-edge walk, weight37560, deficit632|
|7308|012345|16 to15|Obstruction:36-edge walk, weight17224, deficit632|

The original three-edge cycle retains total weight1488 in all five tests. None of these changes lowers its mean496. Rechecking the six saved milestone74 walks and three milestone93 paths was inconclusive for every case. The new bounded integer relaxations therefore supplied the certificates listed above.

For7302, the revised graph has exact minimum cycle mean496: the unchanged cycle attains496, and a potential satisfies

\[
496+\pi(v)\le w(u,v)+\pi(u),\qquad 0\le\pi\le601
\]

on every edge. Its potential range is reported as a sufficient range; this note does not assert range optimality. The corresponding conditional comparison is

\[
4696m\le1098960+8\cdot496+601=1103529,
\qquad
m\le\frac{1103529}{4696}=235-\frac{31}{4696}<235.
\]

Thus a local share floor19 on012034 suffices for this certificate when all other premises are supplied. It reduces the unfinished local target from proving share at least20 to proving share at least19. The new local contradiction target would be share at most18; no such certificate was generated or checked in this task, and no proof-speed improvement is asserted. The original floor20 result remains a sufficient stronger target.

The reduction changes1,043,097 edge weights, each by exactly one. The saved replacement potential was independently checked against all4,947,008 modified edges. The minimum edge slack is zero.

## Why the other four tests fail in this fixed graph argument

Let an admissible constant slope be $\mu$ and a global potential range be $R$. The unchanged cycle gives $\mu\le496$. A saved walk of length $k\le227$ and weight $C$ gives $k\mu-C\le R$. Each listed obstruction has $496k-C=632$, hence

\[
227\mu-R\le(227-k)\mu+C
\le(227-k)496+C=111960.
\]

The current234 criterion requires the strict reverse inequality $227\mu-R>111960$. No choice of constant slope and globally bounded potential can satisfy it on any of those four modified weighted graphs.

This argument does not require that496 be the minimum mean in the obstructed cases. The retained cycle supplies a ceiling on the admissible slope. The witness walks are graph walks, with no claim that they start from permitted initial histories or are realizable in a complete snake. Stronger geometric exclusions, reachable-state restrictions, state-dependent endpoint estimates or a different global budget could alter the conclusion.

## Saved evidence

- `input-pins.json`: file hashes, source-array hashes and the full baseline floor vector.
- `saved-witness-tests.json`: exact re-evaluation of all existing cycles and paths under each one-unit change.
- `case7301.json`, `case7302.json`, `case7303.json`, `case7307.json`, `case7308.json`: each modified profile and its full-key certificates. Witness rows retain edge index, source, target, direction ID, history ID, count code, shape, base weight and modified weight.
- `case7302-potential.i64.gz`: the601-range potential, stored as little-endian signed64-bit values.
- `results.json`: discovery results, exact fractions, time and remaining-premise scope.
- `verification.json`: independent all-edge potential and exact walk checks; status `PASS_INDEPENDENT_FINITE_GRAPH_CERTIFICATES`.
- `test.py`: bounded integer relaxation, using the same potential update and path-deficit argument as milestone74. It checks the pinned source and full-profile arrays before altering weights.
- `verify.py`: independently reconstructs every profile and rechecks the saved certificates without importing the discovery routine or using its distances/predecessors.

Recorded numerical runtime was53.343seconds across saved-witness inspection, discovery and independent verification, below the600-second limit. Five cases were tested. No Lean compiler, SAT/LRAT replay, background daemon or extra numerical case was run.

The remaining local share premises, reference-catalogue premises, complete defined-graph coverage, complete key-dependent weight interpretation and potential replay remain separate. In particular, the computation does not transfer a potential automatically from these saved arrays to conservative extra edges in the graph defined by acceptance tests. The current global interval remains $191\le a(9)\le235$;234 remains conditional.
