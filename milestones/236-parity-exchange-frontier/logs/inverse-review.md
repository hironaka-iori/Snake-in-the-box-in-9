# Independent neighbour-count reconstruction review

Status: the written coefficient identity, change-balance argument and reconstruction deductions are correct. Two small wording refinements are recommended below. No manuscript or note was edited by this reviewer.

## Retained-neighbour balance

For two positive-length induced paths, each retained vertex has selected degree two minus its endpoint indicator. The retained-neighbour terms cancel, leaving the stated equality between added-neighbour count plus the new endpoint indicator and removed-neighbour count plus the old endpoint indicator. Consequently an internal vertex retained as internal has equal added and removed neighbour counts; an old endpoint retained as internal requires one extra added neighbour.

A 192-edge candidate has 96 minority vertices, all internal. Every old internal minority vertex whose two change counts differ must therefore be among the omitted minority vertices. For exactly r minority replacements there can be at most r such old vertices. The old minority endpoint must be handled separately, exactly as the note does.

If an insertion touches a vertex internal in both paths, some deletion also touches that vertex. The insertion and deletion are distinct cube neighbours of the same vertex and therefore are at Hamming distance two. The stated extension `0,1,3,7` to `0,1,3,7,6` is an induced path, independently checked by all vertex pairs, and has no deletion. It correctly disproves an unconditional distance-two requirement on every insertion.

Recommended wording: replace “retained internal minority vertex” in this particular implication by “retained minority vertex internal in both paths.” This makes the endpoint exception explicit at the point where it matters.

## Inverse coefficients and reconstruction

The coefficients `(0,35,0,-10,0,8,0,-16,0,128)` and scale 315 are correct. For a vertex at distance k from the reconstruction target, the coefficient after collecting its contribution is k times the distance-(k-1) weight plus (9-k) times the distance-(k+1) weight, omitting nonexistent boundary terms. Independent exact arithmetic for all ten distances gives:

```text
k:           0  1  2  3  4  5  6  7  8  9
coefficient:315  0  0  0  0  0  0  0  0  0
```

The geometric multiplicities follow because flipping one of the k differing coordinates reduces the distance and flipping one of the other 9-k coordinates increases it. Expanding the finite neighbour sums and collecting these coefficients proves the displayed reconstruction for any real-valued vertex function. No integrality assumption is needed for that written identity. The nonzero diagonal scale then proves uniqueness from complete neighbour counts.

Recommended wording: replace “For odd k, both weights are zero” by “For odd k, every neighbour has even distance, whose weight is zero.” At k=9 there is no distance-10 neighbour and no c10 in the displayed vector. This avoids referring to an absent boundary weight without changing the argument.

For a change function supported on the majority side, the observations on the majority side are automatically zero, and the opposite-side observations on all 256 minority vertices suffice. The reconstruction value at each majority vertex is 315 times its signed membership change. An old selected majority vertex permits changes -1 or 0; an old unselected majority vertex permits 0 or 1. Thus the stated discrete values and membership-sign restrictions are necessary. They do not themselves assert inducedness or path connectivity.

## Complete versus retained counts

The distinction in the note is essential and is stated correctly. The retained minority vertices fix only part of the signed neighbour-change vector. Deleted and previously unselected minority vertices can have nonzero observations and cannot be assigned zero without justification.

The majority side grows from 96 to 97 vertices, so the signed change function sums to one. Every majority vertex has nine neighbours on the minority side, giving total signed neighbour change nine over that entire side. Retained internal minority vertices contribute zero. The unique old minority endpoint contributes one if retained, since it becomes internal; if deleted it contributes to the unprescribed part instead. The remaining observations must therefore sum to eight or nine respectively. These are signed totals, not nonnegative counts. The note does not claim that each unknown observation is nonnegative.

These relations follow from the full degree and change data. Their proposed use as a way to organize choices or reject partial proposals is legitimate; neither a new independent constraint on the complete model nor a demonstrated speed improvement is claimed.

## Finite verification and Lean scope

The inspected verifier computes each entry of K A as the sum of the nine weights on the actual neighbours of its second vertex. The loops cover every pair of labels from 0 through 511. It asserts diagonal entries 315 and off-diagonal entries zero, records exact counts, and hashes the product rows. No random sample or solver is involved.

The saved source hash matches the inspected script. Its 512 diagonal and 261,632 off-diagonal entries sum to 262,144. Independently constructing the expected 315I row bytes reproduces the receipt's matrix-product SHA-256:

`362b02a5241bf1319e4f0cf885a45db0b926982843d531ca96f7075ec7299521`

This review recomputed the ten distance recurrence cases, the expected identity digest and the small path counterexample. It did not repeat all 262,144 inverse-entry calculations.

The inspected `AdjacencyInverse236` source states an integer-valued finite reconstruction lemma with the observation equations, a coefficient identity, distinct column list and membership as explicit premises. Its separate recurrence covers the five even distances. The actual cube neighbour multiplicities, complete labelled lists, and the real-valued identity are supplied by the written argument and finite calculation, rather than being discharged by that generic lemma. `ExchangeBalance236` derives the count relations from Boolean neighbour filters and supplied old/new degree equalities; actual path geometry supplies those degree premises. No compiler result is asserted by this source review.

## Reviewed input pins

- `MATHEMATICAL_NOTE.md` at the inspected pre-publication state: `4b864e766d87cc1dab49bb74f762edf58608b749552096c37aefac6b2bb5bd7e`
- `scripts/verify_inverse.py`: `820637e2a4cc99b3b6fdfe7e3ae3ec519fb055e4f96184c2e07c80e93b0ae2c5`
- `data/inverse-audit.json`: `3490fce8ff88e452a35ad86a2c089053e7c54f55dc832311342483b1c2fe0f4c`

The note is expected to receive numerical results and the two recommended wording refinements later. These pins identify the state reviewed here. No solver, compiler, software test, model mutation or new search was performed, and the active four-exchange worker was untouched.
