# Independent review of the joint share-floor obstruction

The cycle mapping, inequality signs and exact arithmetic pass this bounded review, including the later eleven-cycle extension. The conclusions are necessary conditions for the fixed retained weighted graph. They do not establish a new bound for arbitrary snakes or sufficient share floors for the whole graph.

## Fourteen-cycle mapping

The current 14 rows equal the frozen independently audited rows in milestone144. Their state sequence closes and has 14 distinct vertices. Direction-code lookups and count-code decoding were rechecked against the saved direction model. This review reused the prior source-array audit; it did not reopen the full graph arrays.

The `012301` suffix occurs at zero-based positions 1, 4, 8 and 11. The `012340` suffix occurs at positions 6 and 13. The other eight suffixes are `012304`. Canonicalization includes both orientations. There is no `012034` suffix or occurrence event.

For the first shape, the old weights minus (120) times the stored entering count are (6,11,6,11); for the second, they are (4,4). Thus, when (F\ge11) and (G\ge4), the weights are

\[
(256,240+F,736,496,360+F,736,360+G,
496,480+F,376,736,360+F,496,720+G).
\]

The total is (6848+4F+2G), and the first two sum to (496+F). The final entering-count symbol is 6, representing an actual count at least 6. Accordingly, (720+G) is the clipped graph weight, without an assertion that the actual count equals 6.

## Potential inequalities and the first tradeoff

The evaluator uses (\mu+p_{i+1}\le w_i+p_i). Summing around the cycle and along its first two edges gives, respectively,

\[
7\mu\le3424+2F+G,
\qquad
2\mu\le496+F+p_0-p_2\le496+F+R.
\]

For (\mu\ge0), a comparison below 235 has a positive denominator and implies

\[
111960+BC+R<227\mu,
\qquad
111464-F+BC<225\mu.
\]

Combining this with the cycle cap yields exactly

\[
9848+7BC<457F+225G.
\]

The algebraic tradeoff does not require separate nonnegativity assumptions on (B,C,R). The following exclusions use (BC\ge0):

- At (F=16), one needs (G>2536/225), hence (G\ge12) for an integer floor. The integer conclusion should not be stated for arbitrary real (G).
- At (F=19,G=4), the comparison is at least (235+265/32866).
- At (F=G=16,B=24), a comparison below 235 requires (C<19/3).

The source in `JointFloors145.lean` has the correct inequality directions and quantifiers. Its existing parent receipt records seven passed theorem reports with standard axioms. This review read that receipt and pinned its source; it did not invoke Lean or repeat the complete dependency audit.

Every saved numerical row was independently recomputed:

| (F) | (G) | Cycle mean | Zero-cost comparison lower bound minus 235 |
|---:|---:|---:|---:|
|16|4|\(3460/7\)|\(409/8215\)|
|19|4|\(3466/7\)|\(265/32866\)|
|20|4|\(3468/7\)|\(-16/2739\)|
|16|11|\(3467/7\)|\(61/32867\)|
|16|12|\(3468/7\)|\(-41/8217\)|
|16|16|\(496\)|\(-19/587\)|

After using the two-edge range constraint, the zero-cost fraction is

\[
\frac{1098464-F+10\mu}{4200+\mu}.
\]

Its derivative has the sign of (F-1056464), which is negative for these six cases. Evaluation at the largest allowed mean therefore gives a lower bound for all feasible means. In each saved case, the first two edges also attain the largest proper cyclic-subwalk deficit at the displayed mean. This latter fact was checked only for these six cases; the general tradeoff needs no optimal-range assertion.

## Eleven-cycle extension

The second saved cycle was checked against the frozen milestone144 zero-credit audit. It has 11 edges, total old weight 5399, and exactly four suffix occurrence events at positions 0, 2, 7 and 9. The event test was independently recomputed from the exact stored pair counts. Its suffix shapes are `012032`, `012314` and `012031`, so varying (F), (G), or the `012034` floor leaves its base weights unchanged. Both saved cycles use the same retained-edge set, and every listed edge remains retained.

With uniform occurrence credit (C), this cycle gives

\[
11\mu\le5399+4C.
\]

For (B=24), combining this cap with the fourteen-cycle two-edge range inequality and the strict comparison target gives

\[
11329-11F<636C.
\]

Eliminating (C) with the first tradeoff yields the stronger necessary condition

\[
9074<325F+159G.
\]

Thus, if (F=16) and the eleven-cycle keeps these weights, an integer (G) must satisfy (G\ge25). The earlier requirement (G\ge12) remains valid as a weaker consequence of the fourteen-cycle alone.

At (F=G=16), the two caps and the range constraint imply

\[
24C\ge66\mu-32394,
\qquad
R\ge2\mu-512,
\qquad
\mu\le496.
\]

Consequently,

\[
\frac{1098960+8\mu+24C+R}{4200+\mu}
\ge
\frac{1066054+76\mu}{4200+\mu}
\ge
\frac{551875}{2348}
=235+\frac{95}{2348}>235.
\]

The second fraction is decreasing because its derivative numerator is (-746854). The point ((\mu,C,R)=(496,57/4,480)) satisfies all three scalar inequalities with equality and gives the displayed fraction. This checks attainment for the scalar constraints; it does not provide a potential certificate for the full graph.

`TwoCycles145.lean` agrees with these deductions. Its existing parent receipt records seven passed theorem reports with standard axioms. No Lean process was run for this review.

## Monotonic extension and scope

Each varied edge weight is the maximum of its old weight and (120c+F) or (120c+G), hence is nondecreasing in the floor. For (F\le19,G\le4), the fourteen-cycle weights are bounded above edge by edge by the ((19,4)) weights. Any potential satisfying the smaller-weight inequalities also satisfies the larger-weight inequalities, so the same obstruction follows. This includes floors below the affine regime without substituting them into an invalid affine formula. The analogous extension from ((16,11)) covers (F\le16,G\le11).

The two-cycle result is restricted to unchanged other weights and retained edges. In particular, raising the `012032` share floor changes the eleven-cycle cap. The broader conditional catalogue already strengthens that shape and other floors, so the obstruction does not refute its comparison. Removing an edge of either cycle can also invalidate this argument. Passing either necessary test does not establish sufficient full-graph conditions, actual share theorems, or the graph-to-snake assembly.

Evidence is frozen in `data/joint-floor-review.json`, SHA-256 `eec1b4505b0ceb71c4b81af6524e3ec79f6635262383af0f2e9cf13d04b24883`. Its source map includes both saved cycles, both frozen independent audits, the evaluator, direction model, analysis script, Lean sources, parent compilation receipts and retained-edge files. No solver, optimizer, full-graph computation or delegation was used. Previous bridge files remain unchanged.
