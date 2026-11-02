# Critical-cycle review

This is an independent read-only inspection of the saved numerical cycles and prior local tests. It does not add a local refutation, a share theorem, or a complete graph certificate. No solver or Lean compiler was started. Only the seven indicated graph entries were extracted; the graph was not searched again.

## Exact full keys and weights

The cycle indices come from `109-relaxed-graph-test/data/restricted-profiles.json`. Directions, histories, codes and endpoints were read from `72-four-count-proof-closure/critical-current/build/source-graph.npz`; canonical direction words were read from the direction table. The completed profile uses the proved model in milestone 73, and the conditional profile uses milestone 97's `floor-sensitivity/012034-minimum/floor18.json`.

For a row with direction word $D$ and count code $c$, the six symbols are

$$a_j=\left\lfloor c/6^{5-j}\right\rfloor\bmod6+1\qquad(0\leq j<6).$$

They describe centres $r+3,\ldots,r+8$. The five-centre share is at $r+4,\ldots,r+8$, so its six-transition shape is the last six entries of $D$, with count tuple $(a_1,\ldots,a_5)$. A reversed shape requires the reversed count tuple as well. Every symbol in these cycles is below 6, so all displayed counts are exact; the interval interpretation of symbol 6 is not used here.

### Completed profile

| Original edge | Direction | History | Code | Nine directions | Six counts | Profile weight |
| --- | ---: | ---: | ---: | --- | --- | ---: |
|372796|47|0|33217|012034130|5,2,4,5,5,2|252|
|2610423|258|0|12681|012340325|2,4,5,5,2,4|480|
|3534483|352|16|29434|012342153|4,5,5,2,4,5|600|
|1650991|173|0|36640|012310420|5,5,2,4,5,5|600|

The endpoints chain as

$$114400\to593089\to1147977\to394906\to114400.$$

The total weight is 1932 and the mean is 483. In particular, the third row has history 16; replacing the full key by direction and count alone would discard information. The entering counts are $2,4,5,5$, and the respective added share credits are $12,0,0,0$.

### Conditional profile with the 012034 floor 18

| Original edge | Direction | History | Code | Nine directions | Six counts | Profile weight |
| --- | ---: | ---: | ---: | --- | --- | ---: |
|1131395|108|0|26908|012302432|4,3,5,4,3,5|616|
|2139224|198|0|21483|012314210|3,5,4,3,5,4|496|
|17417|2|0|35588|012031043|5,4,3,5,4,3|376|

The endpoints chain as

$$245540\to454588\to5931\to245540.$$

The total weight is 1488 and the mean is 496. The entering counts are $5,4,3$, and every row receives share credit 16. These are abstract graph cycles; this inspection supplies no realization by an actual snake.

## Shapes and existing exact probes

The following comparison uses simultaneous reversal of directions and counts. Window indices are zero-based positions in the 477-entry `critical-current/data/windows.json` list.

| Profile and direction | Representative six-direction shape | Corresponding five counts | Saved window index |
| --- | --- | --- | ---: |
|completed47|012310|2,4,5,5,2|274|
|completed258|012034|4,5,5,2,4|78|
|completed352|012340|5,5,2,4,5|189|
|completed173, reversed|012034|5,5,4,2,5|122|
|conditional108, reversed|012031|5,3,4,5,3|absent|
|conditional198|012314|5,4,3,5,4|440|
|conditional2|012031|4,3,5,4,3|absent|

Direction 108 has forward suffix `012302` with counts `3,5,4,3,5`. Its smaller reversed representative is `012031` with counts `5,3,4,5,3`. Combining the reversed representative with the forward count tuple would test a different window.

There is no saved `wNNN-*.json` probe for any of the five matching window indices above. An independent comparison against every JSON record under `critical-current/data/probes`, including reversed pairs, found no exact match to any of these seven tuples. The saved UNSAT probe `w471-None.json` has shape `012314` and counts `3,4,5,4,3`; it does not cover the current conditional tuple `5,4,3,5,4`. A window's presence in `windows.json` alone is not a solver result.

The general certificates `general0-cap15-certificate.json` and `general6-cap15-certificate.json` already concern shapes `012031` and `012314`, respectively, with all five count intervals $[0,21]$. Milestone 73's `CombinedCatalogue.lean`, through `canonical7300` and `canonical7306`, supplies the existing lower bound 16 for the sum of the five scale 12 shares, in either orientation. Repeating cap 15 with the exact conditional-cycle counts would therefore supply no larger credit.

## Prior route and smallest useful next test

Cycle-targeted local necessary conditions already appear in the project. Milestone 44 derives the condition $\alpha(r+2)+\alpha(r+6)\geq7$ for the eight-transition pattern $(a,b,c,d,e,a,d,b)$ with distinct labels. It also records why a shorter surrounding pattern is insufficient. This is a precedent for the route, not a claim that the current cycle tuples are excluded.

Milestone 73's `NEXT.md` and milestone 82's unsaturated-cycle note already identify the completed cycle and suggest stronger shape-only floors on `012034` and `012340`. Milestone 97 records the conditional mean 496 and the minimum pending floor combination. The inspected milestone 105 interface preserves full graph keys and the reference-union premise. These sources do not document the exact count-conditioned cap 16 tests below. A narrow search of local branch references, including `origin/research/q9-critical-family-count-exclusions`, also found earlier critical-window restrictions, without an identical test for these tuples. This is a bounded repository search, not an exhaustive prior-art search.

The smallest useful new share experiment is the existing six-transition encoder with shape `012031`, exact counts `4,3,5,4,3`, and share cap 16. If its local formula is UNSAT and the result is checked and transferred to actual snakes, it gives a scale 12 five-centre share lower bound 17 on direction 2's cycle tuple. The other `012031` tuple, `5,3,4,5,3`, is an equally well-aligned target. The first choice has a direct forward match and reuses the already established `012031` geometry. No satisfiability outcome or runtime advantage is asserted.

If this suffix-only test is satisfiable, the saved nine-transition word and all six counts provide the next available context. Its count and share positions must be checked in the encoder and in the actual-snake transfer theorem before using a result. A local SAT assignment need not extend to a full snake. Conversely, a new checked credit on one edge raises this particular cycle's weight, but does not establish a larger minimum mean for the entire graph: other cycles and the potential range must be evaluated and certified again.

All seven rows have counts below 6. Thus a bonus that vanishes whenever all counts are below 6 cannot alter either saved cycle. Parent's broader 143-core screen reports no hit on either cycle; this review did not rerun that screen. Together, these observations favor stronger count-conditioned share on an actual cycle tuple over further testing of the same count-saturation bonus.

## Evidence pins and limits

| Source | SHA256 |
| --- | --- |
|109 `data/restricted-profiles.json`|`b38036cb72850309d8310dd173b79b040164461e2238ad0da73693270a7ad7eb`|
|72 `critical-current/data/windows.json`|`26a26cc441c0f24eff1e7440d6af79ecaad5f2acf37fadefa5726eebac450b8a`|
|72 `critical-current/data/general0-cap15-certificate.json`|`e9c43434ba27a12315c42baf782d33e0c746fa23cb5d1e6e943df543dbd9bd3f`|
|72 `critical-current/data/general6-cap15-certificate.json`|`91938a79b549438e5c30141532346bf64b30624776825ae67b9c03266e342883`|

The restricted-profile receipt additionally pins the source graph to `b40f1ca44ad8f3269f890efe8decc60f19dabd647f11255c05df3727341c2c34`, the completed model to `785956145396df7cf6230c446a9e7469b7c4b1713c6cf70d21a9091f1c8f7907`, and the conditional floor 18 model to `32090c554c40b97f1c656099ae10b935758ddb2575024d18cd69567ee71a6294`. These three hashes are recorded receipt values; this bounded review did not rehash the large graph. No new upper bound follows from this report.
