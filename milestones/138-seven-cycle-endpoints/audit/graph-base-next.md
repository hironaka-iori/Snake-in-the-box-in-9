# Next graph update from the exact nine-direction exclusion

This separate note concerns the theorem `actual_cycle_row` in `ActualBase138.lean` only. The stronger six-direction cap rule in `graph-next.md` remains a separate proposal. This review read source files and saved JSON rows; it did not load graph or potential arrays, run a solver, or run Lean.

## Exact theorem interface and mask

The inspected source is in namespace `Snake9.LocalWindow.CycleBase138`. Its theorem `actual_cycle_row` has an actual snake of arbitrary length, a fitting nine-transition window, canonical chronological directions `012301430`, and these count conditions:

\[
\alpha_{r+3}\ge 6,\qquad
(\alpha_{r+4},\alpha_{r+5},\alpha_{r+6},\alpha_{r+7},\alpha_{r+8})
=(3,3,3,5,2).
\]

Here the counts are the existing `coreAlpha` values; no additional mathematical quantity is introduced. The source imposes neither an endpoint restriction nor a parity restriction. Its full eight internal bounds are `(0..21,0..21,6..21,3,3,3,5,2)`. The source derives the universal upper bound 21 for the otherwise unrestricted internal positions.

At this review, the parent is checking the proof. This note inspects the theorem interface and records no independent compiler success. Use the deletion as a proved ordinary exclusion only after the complete certificate, semantic bridge, and final actual-snake theorem have passed with pinned final sources.

The graph row stores six symbols for local vertices 3 through 8. Therefore the minimal forward mask is precisely:

```python
base_shape = np.array([
    canon(word) == (0,1,2,3,0,1,4,3,0) for word in ds
])[arrays['direction']]
base_reject = base_shape & np.all(
    digits == np.array([6,3,3,3,5,2]), axis=1
)
mask = keep & ~odd_reject & ~six_reject & ~base_reject
```

This is a proposed implementation fragment, not code executed during this review. Symbol 6 means an actual count in `[6,21]`, exactly as required by the first count condition. Symbols 2, 3, and 5 are exact. There is one placement of the full nine-direction word in a nine-direction row. This mask does not test the two shorter six-direction placements.

No new charge or weight is warranted. Preserve the old shared maximum, both weight profiles, and all inherited assumptions. The mask removes edges from both profiles.

## Reversal requires different count positions

The reversed nine-direction word happens to canonicalize to `012301430` again. Nevertheless, reversing the six stored count symbols is not justified. The stored positions 3 through 8 of the reversed nine-window correspond to original positions 6 through 1. Two of those counts, at original vertices 1 and 2, are absent from this row.

In the original chronological indexing, the reversed theorem would require counts `(2,5,3,3,3,6..21)` at vertices 1 through 6. The available vertices 3 through 8 cannot check these hypotheses. The minimal proposed mask therefore applies the chronological theorem once, with the forward count pattern above. It introduces no reverse-count shortcut.

## Saved-cycle effect

All four saved profiles below were checked against the canonical full-nine word and the six exact stored symbols.

| Saved profile | Cycle length | Matching full-nine rows | Deletion by this rule |
|---|---:|---|---|
| milestone131 `completed` | 4 | None | None |
| milestone131 `conditional_floor18` | 7 | Row 5 only | Edge 992157 |
| milestone121 `completed` | 18 | None | None |
| milestone121 `conditional_floor18` | 4 | None | None from this rule alone |

The matching seven-cycle row has direction ID 95, directions `012301430`, and count symbols `(6,3,3,3,5,2)`. Its deletion breaks that saved cycle. Edge 1273862, row 6, is retained by this exact rule. Its deletion belongs to the stronger shorter-window cap proposal and cannot be imported into this experiment without that additional theorem.

The completed four-cycle retains edge IDs `2222328`, `147674`, `2220858`, and `146782`, with unchanged weights `480`, `496`, `360`, and `616`. Their sum is 1952 and their mean is 488. The old all-edge potential stays valid after edge deletion, while this attaining cycle survives. Thus the exact completed graph minimum remains 488 under this update, with unchanged preceding weights and hypotheses. This is a finite-graph consequence; it is not a new actual-snake upper bound.

The conditional minimum stays at least 496 by its old potential. A new attaining cycle and all-edge certificate are required to decide whether the minimum strictly increases. The archived 18-cycle also survives, so its existing milestone131 comparison mean \(3011/6\) remains valid. Its older milestone121 weight evaluation \(2915/6\) must remain distinguished.

The earlier milestone121 conditional four-cycle is listed only as a test of this new rule. Its inclusion here does not assert survival under intervening milestone131 changes. Global deletion counts were not computed.

## Exact source hooks and next check

- Add the mask before retained-edge extraction at milestone131 `scripts/evaluate_graph.py` lines 347–350, corresponding to `scripts/prepare_graph.py` lines 162–165. Keep both old bonus calculations and weight profiles unchanged.
- Use order-sensitive `canon` from evaluator lines 101–103 and the six-symbol decode at line 156. Do not reuse a shorter-window slice or reverse its count array.
- Preserve milestone131 and generate the next experiment separately. Its generator must reproduce its generated evaluator; the existing preparation splice is at lines 248–258.
- Reproduce the milestone121 checks already present at evaluator lines 256–267 and add a full predecessor131 mask/weight comparison before the new deletion. Pin the final base proof and actual theorem receipts, the exact generator, and all immediate predecessor inputs.
- The archived 18-cycle survival and mean checks at evaluator lines 353–359 remain appropriate for this rule. Retain all-edge inequalities, attaining-cycle and overflow checks at lines 361–413, together with resource and timeout records.
- Record this exclusion as an exact nine-direction rule with no new weight. Continue to state the inherited pair, six-count, and profile hypotheses and the remaining graph-to-snake assembly. The conditional profile is the next useful minimum computation; the surviving four-cycle already determines the completed mean.

## Inspection hashes

These SHA-256 values pin the bytes inspected here. The source and proof-plan pins are inspection snapshots; final proof completion must be established from its actual receipts.

| Repository-relative path | SHA-256 |
|---|---|
| `milestones/138-seven-cycle-endpoints/lean/ActualBase138.lean` | `c9178cc9493a09b34fdfde1ea3675ad2c5f213f7cfa658dd9fcf8cde2eca08ab` |
| `milestones/138-seven-cycle-endpoints/data/proof-plan-base.json` | `20863f459ee8cf7371783c1146b72bf28a8ea59d71161349a1bfea91bb0d5128` |
| `milestones/138-seven-cycle-endpoints/work/base/encoding.json` | `82068cbaec8e5f17417510d5c3bd013dc022f50e109dbe97aadf7ae48f2d3ac0` |
| `milestones/131-odd-pair-six-count/scripts/evaluate_graph.py` | `86386a1a117dfd9080b7360f9b99a641054fe9ea174baa9a2b532b33199e52ac` |
| `milestones/131-odd-pair-six-count/scripts/prepare_graph.py` | `ea9c46904e1ef1dcccf279cb48d235bde3662902857977d5b0fe160461595391` |
| `milestones/131-odd-pair-six-count/data/odd-pair9-six25/results.json` | `157c1cd0751b487e220b954f441670839c50078167f54c83557f43f98fb8fd2d` |
| `milestones/121-replacement-window-pressure/data/pair-graph/results.json` | `7492ff3a45178740d3253c679bcdd2f5e7907be907f055f455e739cde0b327bf` |
