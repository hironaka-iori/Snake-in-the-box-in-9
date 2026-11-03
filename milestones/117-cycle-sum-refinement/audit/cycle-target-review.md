# Three bounded count-sum targets

## Scope and decoding

The reviewed cycles are the final universal-total-22 experiment from milestone 115: 26 edges with completed-floor mean $6309/13$, and 6 edges with conditional-floor mean $496$. I independently decoded their 64 window placements from the saved full direction/history/count keys and the 505-word direction table. The decoded words, count order, reversal flags and full edge records agree with `115/data/universal-cycle-audit.json` and `115/data/universal345-total22/results.json`.

For a six-transition word beginning at $x_r$, write the five counts as $(\alpha_{r+1},\ldots,\alpha_{r+5})$. Placement zero takes directions 2 through 7 of the nine-transition extension and the first five count digits; placement one takes directions 3 through 8 and the final five digits. Coordinate relabelling and reversal are applied jointly to directions and counts. All tuples used below have digits below six, so they are exact counts, not interval representatives.

The completed cycle uses shapes $012032,012034,012310,012314$; the conditional cycle uses $012034,012301,012304,012310$. Their common shapes are exactly **$012034$ and $012310$**. The empty shared-suffix summary in the older audit combines several experiments; it must not be read as saying these final two cycles have no shared shape.

The JSON companion stores every distinct tuple on these common shapes, its original edge indices and placements, the three target tests, prior counterexamples and source hashes. This review did not repeat the whole-graph potential checks, local-witness adjacency checks, solver runs or Lean checks.

## Ranked targets

### 1. $012034$: middle at most five, outer sum at least sixteen

Test the candidate

$$
\alpha_{r+3}\le5\quad\Longrightarrow\quad
\alpha_{r+1}+\alpha_{r+2}+\alpha_{r+4}+\alpha_{r+5}\ge16.
$$

The negative probe uses ordinary bounds $[0,21]$ except middle $[0,5]$, and an outer-four sum at most 15. It requires the existing four-count counter and one cap. These are the offending exact tuples:

| Profile | Tuples on $012034$ |
|---|---|
| Completed | $(3,3,5,5,4)$, $(3,4,5,5,3)$, $(3,5,5,3,4)$, $(5,4,5,3,3)$ |
| Conditional | $(5,2,5,4,4)$ |

Every tuple has middle 5 and outer sum 15. The condition hits **16 placements on 14 completed-cycle edges** and **4 placements on 4 conditional-cycle edges**. One representative completed occurrence is edge 230218, placement one, with tuple $(3,5,5,3,4)$. A conditional occurrence is edge 2943379, placement one, jointly reversed to $(5,2,5,4,4)$.

This is the first priority because it removes both saved obstructions using a smaller counter than an unrestricted five-count refinement. None of the reviewed local witnesses contradicts it. During this review, the parent completed this exact probe: `117/data/probes/012034-middle5-outer15.json` records `UNSAT_UNCERTIFIED`, 5.765 seconds and no added cycle cuts. This record is native evidence only; it does not supply the needed checked contradiction and actual-snake transfer.

### 2. $012034$: all counts at most five, total at least twenty-one

Test

$$
\bigl(\alpha_{r+j}\le5\text{ for }1\le j\le5\bigr)
\quad\Longrightarrow\quad
\sum_{j=1}^{5}\alpha_{r+j}\ge21.
$$

The negative probe has five bounds $[0,5]$ and total at most 20. Besides the four completed tuples in target 1, it hits

$$
(5,3,3,5,4),\qquad(5,4,3,3,5),\qquad(5,5,3,3,4).
$$

The same conditional tuple $(5,2,5,4,4)$ is hit. The counts are **28 placements on 22 completed-cycle edges** and **4 placements on 4 conditional-cycle edges**. Thus this candidate has a larger effect on the saved completed cycle than target 1, but uses more count assumptions and the larger five-count counter. It is ranked second, not presented as logically implied by target 1.

The unrestricted total-at-most-20 probe in milestone 112 was UNKNOWN. The new bounded attempt is also UNKNOWN, and the parent's cap-five version `117/data/probes/012034-caps5-total20.json` is UNKNOWN after 12.047 seconds. A timeout is not a counterexample. The known cap-five local witness $(5,5,4,5,5)$ has total 24 and therefore does not refute this candidate.

### 3. $012310$: second and fourth counts exactly five, total at least twenty-one

Test

$$
\alpha_{r+2}=\alpha_{r+4}=5
\quad\Longrightarrow\quad
\sum_{j=1}^{5}\alpha_{r+j}\ge21.
$$

The negative probe has bounds $[0,21],[5,5],[0,21],[5,5],[0,21]$ and total at most 20. It hits:

| Profile | Tuple | Exact occurrences |
|---|---|---|
| Completed | $(3,5,4,5,3)$ | edge 1608674, placement one; edge 237832, placement zero |
| Conditional | $(4,5,2,5,4)$ | edge 933649, placement one; edge 1335229, placement zero |

Both tuples total 20. The condition is invariant under joint reversal and uses the existing total-count counter. It provides a distinct shape to test if the first two refinements leave new cycles. No reviewed probe establishes this candidate. Its exact adjacent-count assumptions intentionally exclude the known counterexamples to a universal $012310$ total lower bound of 21. I make no minimality or likelihood-of-truth claim for this hypothesis.

## Existing counterexamples and limitations

Milestone 112's independently audited local witnesses on $012310$ include:

- $(4,5,3,4,4)$, total 20 and outer sum 17, with component sizes $76,15,15,7$;
- $(3,6,4,4,3)$, total 20 and outer sum 16, with component sizes $45,27,15,15,7,1,1$.

The first invalidates an unrestricted total-at-least-21 claim even when all five counts are at most five. Together they also invalidate the proposed implications “middle at most three forces outer sum at least eighteen” and “middle at most four forces outer sum at least seventeen.” Both have fourth count four, so neither contradicts target 3. Their reversals likewise fail its exact second-and-fourth condition.

Milestone 113's audited $012034$ local witnesses include $(10,4,4,3,6)$, $(5,5,4,5,5)$ and $(6,5,4,5,3)$. Consequently central caps alone cannot simply be declared impossible; all-five upper caps five are locally feasible; and the old central caps $(5,4,5)$ cannot force the outer pair above nine. These witnesses have middle count four, so they are not counterexamples to target 1, and their totals exceed 20, so they do not refute target 2.

These are counterexamples to deductions from the relaxed local model. They are disconnected forests, not counterexamples constructed as complete snakes. Native UNSAT records are likewise insufficient to declare a new actual-snake theorem. Retain the distinction throughout subsequent proof work.

## Bounded stopping rule

Stop selection after these three ranked targets. Target 1 is ready for certificate work based on the parent's native result. Target 2 has a bounded UNKNOWN record and should not be silently rerun without a changed proof strategy or explicit new resource budget. Target 3 is one exact proposed test; an audited local witness would reject it for this local model.

After any successful exclusion, first establish the exact semantic statement and a checked contradiction before asserting an actual-snake consequence. Native graph experiments may be labelled conditional while that is pending. Hitting one edge of each saved cycle only removes those particular obstructions; it does not prove either minimum mean increases, because other attaining cycles may survive. No further coefficient search or unrelated local family is recommended by this bounded review.

Companion JSON SHA256: `08512af0445aa955e7ddf002f32d0ef80bb83a274dd7e85a68a3be0926b9d96b`.
