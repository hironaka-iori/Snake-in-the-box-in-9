# Aggregation and weighted-overlap review — 2026-10-31

This review proves conditional arithmetic and search/aggregation rules. It also independently excludes one specific seven-edge finite-model walk. It does not prove the complete arbitrary-snake interpretation of milestone72, eliminate all minimum-mean cycles, or establish a new global Q9 upper bound. No upload was performed.

Inputs: `upstream_proved_analysis.json`, copied from `milestones/72-four-count-proof-closure/data/proved-analysis.json`. Its SHA256 is `33cd5aedbb10054a7873c9fcd4a241396303757ca0d83d195c3fea51b009503a`. The JSON itself explicitly says that the complete arbitrary-snake graph interpretation remains pending. I have checked the displayed cycle, arithmetic and overlap reasoning, not replayed its 4,957,613-edge potential certificate.

## 1. Exact threshold and endpoint bookkeeping

Assume the supplied global inequality is valid for the number m of snake EDGES:

    m <= (1098960*d + 8*p + R)/(p + 4200*d),

where p,d>0, mu=p/d, and R>=0 is the potential range in the same integer scaling as p,d. Excluding 235 edges requires the STRICT inequality

    227*p > 111960*d + R,

or equivalently

    mu > (111960 + R/d)/227.

For d=1 and R=578 this is mu > 112538/227, approximately 495.762115. An integer mean 496 is sufficient; 495 is insufficient. At 496 the bound is 551753/2348 = 235-54/4696, hence integer m<=234. At 495 the bound is 1103498/4695 >235. Equality at the threshold gives only m<=235; it does not exclude 235. The code checks this using exact fractions, not floating tolerances.

At the recorded p=480,d=1,R=578, the result is exactly 551689/2340 and floor 235, agreeing with the upstream JSON. Even R=0 cannot make mu=480 exclude 235: 227*480=108960<111960. Thus reducing only the current range cannot achieve the desired next bound under this formula.

For rational means keep the d term explicitly. Multiplying p,d by k requires multiplying R by k as well for an equivalent certificate; changing only p,d spuriously improves the boundary term. If one genuinely has R=578 in the certificate's chosen integer units, mu=496 suffices for every integer d>=1, but the primitive mean/range pair must come from a verified certificate.

The constants 1098960 and 8 are assumptions in this review. The upstream summary JSON does not supply their geometric derivation. In particular, the term 8p is consistent with a lower-bound telescoping calculation over m-8 transitions, but this interpretation must be checked against the actual automaton-to-snake map; it is not proved merely by recognizing the algebra. If the bound counted vertices rather than edges the rounding claim would shift by one. Endpoint vertices must not be silently reclassified as internal centers, and changing an endpoint allowance changes the coefficient of p. No endpoint improvement is claimed here.

## 2. Turning prefix pruning into a global result

Let a complete family of valid prefixes P cover every candidate global snake, possibly modulo explicitly proved cube automorphisms and reversal. If a prefix has ell vertices and the rooted residual bound B(P) counts its head, then

    final number of edges <= ell + B(P) - 2.

To exclude a 235-edge snake, every covered prefix must have B(P)<=236-ell, or every branch must be exhaustively continued to an independently checked rejection. A favorable bound for one prefix is not a bound on another prefix or on the maximum over all prefixes. A finite proof tree is sufficient only if its branching is exhaustive, all pruning rules are sound, and every leaf is rejected or below target. UNKNOWN leaves prevent the exclusion.

A global sum of local claw losses is also invalid without an explicit shared resource budget. The same omitted cube vertex can satisfy many prefix/window constraints. Disjointness within one residual graph, or a dual coverage condition within it, proves a bound for that prefix; it does not automatically control the total across many different prefixes or positions of the final snake.

## 3. Weighted overlapping-claw dual: valid with exact checks

Fix one rooted residual graph R and its head h. Let x_v=1 when v is omitted by a candidate induced continuation and x_v=0 when selected. For a four-vertex group containing a center and three of its neighbors,

    sum_{v in group} x_v >= 1.

The group need not induce a claw: the three center-neighbor edges alone ensure degree three if all four vertices are selected. For the endpoint-star group {h} union N_R(h), the bound is

    sum x_v >= max(deg_R(h)-1,0),

because h is selected and can have at most one selected neighbor. This second inequality depends on the fixed head being an endpoint. It is not valid for an arbitrary path passing through an internal h.

Give every valid group g a nonnegative rational weight lambda_g and its proved loss b_g. Require the exact per-vertex inequalities

    sum_{g containing v} lambda_g <= 1 for every v in R.

Multiply each group inequality by lambda_g and add. Since x_v>=0,

    sum_v x_v >= sum_v x_v * sum_{g containing v} lambda_g
                 >= sum_g lambda_g*b_g.

Therefore the rooted continuation has at most

    |R| - ceil(sum_g lambda_g*b_g)

vertices. Overlaps are safe precisely because of the per-vertex coverage bound. Taking the minimum with independent leaf, parity and block bounds is safe; adding their omission penalties without a joint coverage argument is not.

A numerical LP solution is a candidate certificate only. Store exact rational numerators/denominators; recheck nonnegativity, every group definition and loss, every vertex's coverage, and the exact objective using Fraction or integer cross-multiplication. Small floating tolerances are insufficient to justify a final floor/ceiling. Duplicated groups are harmless if coverage is counted with multiplicity; silently deduplicating coverage while retaining duplicated objective weights is unsound.

A simple strict-improvement illustration is the five four-subsets of K5, each supplied a valid degree-three center and weight 1/4. Each vertex has coverage exactly 1. The dual gives omission >=5/4, hence at least two omitted vertices, while a disjoint four-set packing has only one group. The example demonstrates the mathematics of overlap, not a measured Q9 improvement; a forced endpoint-star can dominate it in an actual rooted instance. Exact tests check all feasible omission subsets and reject weights 1/3 because coverage would exceed one.

## 4. Specific milestone72 attaining cycle: a valid seven-edge exclusion

The displayed four directed edges form a closed cycle and have weights 480,360,600,480, mean 480. Their nine-transition canonical direction words are read directly from the source JSON.

Independent lifting takes each next word's first eight symbols and equates them position-by-position with the previous word's last eight literal coordinate directions. Every such eight-symbol overlap contains all six symbols used in its nine-symbol word. Its coordinate map is therefore completely determined and injective. There is no symbol outside the overlap that can be assigned to a fresh seventh, eighth or ninth cube coordinate. Initial embeddings into Q9 can be arbitrary injective coordinate maps; they preserve the Hamming-distance conclusions below.

For all four starting phases, seven consecutive graph edges following this four-cycle produce fifteen literal transition directions with the same first/last coordinate pattern as an eight-periodic word. Phase zero gives

    0,1,2,3,4,2,1,5,0,1,2,3,4,2,1.

The xor over those fifteen directions is a unit coordinate vector. The endpoints of this fifteen-edge cube walk are adjacent, so the walk cannot be part of a snake. The independent program verifies all four phases; their xor masks are 32,32,8,4 respectively. Over sixteen transitions the xor is zero. It also checks every nonconsecutive vertex pair within each fifteen-transition walk: the only pair at distance at most one is (0,15). In particular the first fourteen transitions give an induced path, so this geometric argument cannot justify banning a shorter six-edge occurrence.

General lemma: if a literal coordinate word of period p>=2 is repeated, any initial 2p-1 transitions have xor equal to the last direction of one period, because two complete copies cancel coordinatewise. Their endpoints are adjacent at path-index distance 2p-1>=3, a forbidden chord. The complete 2p transitions instead repeat a vertex. This concerns literal coordinate repetition; a periodic canonical normalized word does not by itself establish literal repetition. Here the unique overlaps were explicitly reconstructed, including the four-cycle's nontrivial coordinate permutation after a single turn.

`check_attaining_cycle.py` and `attaining_cycle_review.json` contain all overlap maps and phase witnesses. `check_aggregate_review.py` also verifies the general xor identity for 9,837 short periodic words.

## 5. What this evidence permits, and what remains

The new valid object is a forbidden length-seven edge walk, in all four cyclic phases of this exact recorded cycle. Do not delete one of its individual edges, prohibit a single four-edge tour, or claim that every periodic automaton cycle is geometrically impossible. The first fourteen literal transitions are themselves an induced path, and the source graph's count/history interpretations still need their separate bridge.

One can add these finite forbidden edge patterns to a higher-memory automaton, for example by tracking the preceding six edge IDs, while proving that every genuine snake's mapped walk avoids them. One must then recompute and independently check the minimum-mean/potential certificate for the resulting language. Other mean-480 cycles or other low-mean cycles may survive. Removing one attaining cycle does not prove a strict increase in the minimum mean.

For an actual improved numerical bound, a sufficient final certificate is: (a) a complete genuine-snake walk map respecting all new exclusions; (b) exact potentials with edge inequalities d*w(e)-p >= Phi(head)-Phi(tail), with the sign convention consistently checked; (c) their actual range R and the exact endpoint calculation; and (d) 227p>111960d+R. Summing the edge inequalities yields the required path-weight lower bound with a possible loss of at most R. The existing single attaining-cycle exclusion supplies one useful ingredient in (a), not the remaining certificate.

Tests and receipts are in `aggregate_review_checks.json` and `attaining_cycle_review.json`. All reported checks PASS. No new numerical upper bound is claimed.

### Registered seven-edge patterns (frozen source edge IDs)

- Phase 0: [3416157,1822955,734195,4462580,3416157,1822955,734195]
- Phase 1: [1822955,734195,4462580,3416157,1822955,734195,4462580]
- Phase 2: [734195,4462580,3416157,1822955,734195,4462580,3416157]
- Phase 3: [4462580,3416157,1822955,734195,4462580,3416157,1822955]

These IDs are meaningful only for the exact upstream graph indexing that generated the source JSON. Match the complete seven-ID sequence, including order and multiplicity. Their total single-tour weight is 1920. If the original potential inequalities at mean480 are verified, the four slacks are nonnegative and sum to zero by telescoping, so every edge in this tour is tight. This still gives no permission to remove any individual tight edge; only the complete forbidden seven-edge histories are excluded by the new geometric proof.
