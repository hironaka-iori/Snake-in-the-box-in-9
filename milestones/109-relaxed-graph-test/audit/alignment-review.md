# Alignment of the relaxed exclusion with full graph keys

This is a bounded source review plus a small computation on the 505 direction words. No Lean compiler, graph mutation, accepted-key enumeration, solver, or proof replay was run. The parent owns the enumeration of the saved diagram's accepted keys.

## Full-key coordinates

The graph row is `(di, qi, code)`, in that order. For an actual snake step starting at transition index $r$ with $r+9\le m$:

- `extensions.getD di []` decodes to `canon (dsOf p r 9)` and has nine transition directions.
- The six symbols of `code` are the truncated counts at centres $r+3,r+4,\ldots,r+8$, in that order.
- For $0\le j<6$, the decoded symbol is

$$
a_j=\left\lfloor\frac{\mathrm{code}}{6^{5-j}}\right\rfloor\bmod6+1
   =\min\{6,\alpha_{r+j+3}\}.
$$

Thus `code % 6 + 1` is the last stored count, at centre $r+8$. The source uses `code / 6` for its five-count code, and the target uses `code % 7776`. The history index updates through `builderNext qi di`; it does not shift the six count positions within this edge.

Relevant sources: `77-direction-state-coverage/lean/ActualDirectionIds.lean:9,35` defines and decodes the direction index; `78-numeric-history-transition/lean/StateWalk.lean:9–16,25–36,46–50` defines the count codes, their source/target relation, and endpoints. `79-retained-edge-guards/lean/IntervalGuards.lean:8,18` defines a digit and proves its actual-count meaning. The authoritative row order is `87-retained-array-membership/lean/RetainedEnumeration.lean:6–14`; `ArrayAssembly.lean:9–11` supplies the argument-order conversion to endpoint and numeric-acceptance functions.

## Exactly two eligible offsets

Let $D$ be the decoded nine-direction list. The exclusion has six transitions and five internal centre counts. The existing reference and interval conventions use a count offset $s$ and the direction slice

```text
slice = D.drop (s + 2) |>.take 6
```

The five centre symbols are $a_s,\ldots,a_{s+4}$. The fitting condition is $s+5\le6$, hence **$s=0$ or $s=1$**.

| Count offset | Direction indices, inclusive | Actual window vertices | Actual five centres |
|---:|---|---|---|
| 0 | 2 through 7 | $r+2$ through $r+8$ | $r+3$ through $r+7$ |
| 1 | 3 through 8 | $r+3$ through $r+9$ | $r+4$ through $r+8$ |

Although a six-direction word fits at direction offsets 0, 1, 2, and 3, the first two do not have all required constrained counts in this edge. Relaxing the two middle counts does not enlarge the eligible offsets: the exclusion still constrains both extreme internal centres, in either orientation. At direction offsets 0 or 1, one of those extreme counts lies before the stored range. The history index contains direction-history information and does not provide that missing count. Any attempt to use such offsets needs an additional theorem or additional state information.

This alignment is established by `CountWindows.lean:25` (`canonical_nine_slice`), `:32–49` (`sixSymbols`, `actual_symbol_slice`), and `:64` (`actual_code_slice`). The exact-key reference definitions in `85-reference-catalogue-union/lean/ReferenceInterface.lean:43–49` use the same `s+2` shift.

## Forward and reversed tests

At each eligible $s$, the forward forbidden condition is

```text
canon(slice) = [0,1,2,3,0,4]
and a[s] <= 2 and a[s+3] <= 2 and a[s+4] <= 3.
```

The reversed forbidden condition is

```text
canon(slice.reverse) = [0,1,2,3,0,4]
and a[s+4] <= 2 and a[s+1] <= 2 and a[s] <= 3.
```

For the reverse test, the canonical pattern of the forward-oriented slice is equivalently `[0,1,2,3,4,1]`. The direct reverse-then-canonicalize test is the existing Lean convention. Reverse only the six-transition slice, and reverse the five centre positions with it. Reversing the whole nine-direction word while retaining the same offset is a different operation.

Expanded tests, using zero-based positions in the six-symbol code:

| Offset and orientation | Count inequalities |
|---|---|
| $s=0$, forward | $a_0\le2,\ a_3\le2,\ a_4\le3$ |
| $s=1$, forward | $a_1\le2,\ a_4\le2,\ a_5\le3$ |
| $s=0$, reverse | $a_4\le2,\ a_1\le2,\ a_0\le3$ |
| $s=1$, reverse | $a_5\le2,\ a_2\le2,\ a_1\le3$ |

Each count test must be paired with its own shape test. Counts at the two unconstrained positions need no extra restriction beyond their encoded range 1 through 6. Symbol 6 represents all actual counts from 6 through 21; it must not be treated as the exact count 6. Caps 2 and 3 are below 6, so their tests on truncated symbols are equivalent to their tests on actual counts. The default upper cap 21 imposes no additional condition on an encoded symbol.

`IntervalGuards.lean:32` proves precisely this truncated-interval equivalence. Its `intervalHit` at line 37 maps reverse centre index $i$ to $s+(w-1-i)$. Applying its existing `encoded_interval_forward_exclusion` and `encoded_interval_reverse_exclusion` at lines 42 and 66 with $w=5$ and the closed `relaxed_reference_refuted` theorem gives the intended actual-snake exclusion. All endpoint conditions on the five interval bounds hold: their lower endpoints are 0 and their upper endpoints are 2, 21, 21, 2, and 3. These generic lemmas also account for reversal of the actual path and its centre counts.

For a new Lean wrapper, first rewrite the direction lookup with `Direction77.direction_decode`; use the generic interval exclusion with the matching orientation and $s\in\{0,1\}$. The source already supplies the needed actual direction and digit alignment. This report has not compiled such a wrapper.

## Applying the test to the defined graph

Use every bounded full key accepted by `DefinedGraph92.diagramKeep retainedDiagram di qi code`, retaining its particular history index. The graph's class lookup is keyed by `75*di+qi`; missing classes reject. The additional exclusion depends on `di` and `code`, but accepted-key membership can vary with `qi`. Do not count a direction/count pair only once across histories or merge distinct keys sharing the same endpoints.

The defined graph's original acceptance need not equal `numericKeep` pointwise. `defined_graph_covers` establishes the needed inclusion of retained numeric keys in the diagram-defined rows. Therefore testing only `numericKeep` keys could omit diagram-accepted edges. The parent's full accepted-key enumeration is the appropriate finite target for measuring additional exclusions from the current graph.

Sources: `92-full-witness-batch/lean/DefinedProofGraph.lean:11–22` defines diagram acceptance and rows, and `:24–34` proves the inclusion. `87-retained-array-membership/lean/RetainedEnumeration.lean:21` states the exact bounded generated-row membership criterion. `88-retention-diagram-certificate/lean/DigitReconstruction.lean:11–21` fixes the diagram digit order and reconstructs every bounded code. The older exact-key guards in `87-retained-array-membership/lean/NumericRetention.lean:11–22` and the interval proposition at `79-retained-edge-guards/lean/IntervalGuards.lean:37` agree on offset and orientation.

The new local exclusion is supplied by a closed milestone108 theorem. It does not depend on the unproved remainder of the reference union. Existing theorems mapping every actual snake into the full retained graph retain their own stated catalogue and coverage requirements. A successful numerical filter test alone does not replace those requirements, certify a modified graph, or yield a new upper bound.

## Small independent shape comparison

Parsing only the 505 nine-direction words in the saved `DirectionTables.lean` and canonicalizing the eligible slices gives:

| Count offset | Orientation | Matching direction IDs |
|---:|---|---:|
| 0 | Forward | 51 |
| 0 | Reverse | 63 |
| 1 | Forward | 49 |
| 1 | Reverse | 55 |

These are counts of direction words before applying history compatibility, code conditions, or diagram acceptance. The sets may overlap across placements and must not be summed as counts of graph edges. This small computation also confirmed the reverse canonical pattern `[0,1,2,3,4,1]`.

The inspected direction-table SHA-256 is `11d3bc9766036ae57fd7eff847143c7b78ddf3fbc9f792a3086003d2c97ea1d8`. No assertion about the number of deleted accepted keys is made by this review.
