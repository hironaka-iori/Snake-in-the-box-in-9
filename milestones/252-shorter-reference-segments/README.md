# Round 252 · Long arms retaining 68 reference edges

The exact maximum for a single-crossing join with a long arm in this catalogue is 191 edges. The opposite arm may be any induced path compatible with the crossing.

The 22 eight-dimensional reference paths have 645 places to retain 68 consecutive edges. Up to coordinate permutation, translation and path reversal these give 212 distinct segments. Allowing both ends to grow freely gives exactly 63 induced paths of lengths 96 through 98 up to these symmetries. The catalogue contains 55 shapes of length 96, seven of length 97 and one of length 98. [Complete census and ordered new parents](census-68.json) · [Independent enumeration](replay-core-68.json)

## Why the census is complete

In the first enumeration, a vertex may be added to a path end if it is unused and adjacent to exactly one occupied vertex, namely that end. Every completion of a chosen segment can be built by adding its left tail first and its right tail second. All intermediate paths are contiguous parts of the completed path. [Enumerator](Grow.cs) · [Input, provenance and all-pairs checks](census.py)

The second enumeration grows the two tails independently. When their combined length is sufficient, it checks every pairing of the required lengths. Once each tail together with the central segment is induced, the combined path is induced exactly when no vertex of one added tail equals or neighbours a vertex of the other. All pairs in the ordered path occur either in one of the two individual extensions or between those outer tails. This argument includes empty tails. The verifier matched the full set of 63 identifiers with the first method. [Two-tail enumeration](ReplayCore.cs) · [Verifier](replay_core.py) · [Indexed criterion](TwoTails252.lean)

## When new shapes appear

Each shape found at 72 retained edges still occurs at 68. The 35 additional shapes consist of 33 of length 96 and two of length 97. For each new shape, the search compared every longer contiguous segment with all 22 reference paths in both orientations. A shape having a longest match of length $s$ belongs to every catalogue with retained length at most $s$. This gives every intermediate count.

| Edges retained | Long shapes | Shapes of length 96 | Shapes of length 97 | Shapes of length 98 |
|---:|---:|---:|---:|---:|
| 72 | 28 | 22 | 5 | 1 |
| 71 | 37 | 30 | 6 | 1 |
| 70 | 42 | 35 | 6 | 1 |
| 69 | 52 | 44 | 7 | 1 |
| 68 | 63 | 55 | 7 | 1 |

The comparison measures consecutive shared edges. Two paths may also overlap in several separated segments. [72-edge comparison](../251-eighty-edge-segments/README.md) · [Full reference-to-shape incidence](origins.json)

## What the 98-edge parent and shorter parents have in common

The archived 98-edge parent, donor 20, generates **exactly the same set of 53 long shapes** as each of twelve other references. Those include the 96-edge donors 15, 16 and 17. Each of these thirteen references generates all 35 additions to the earlier catalogue. Thus the 98-edge parent's weak performance when kept intact does not prevent it from supplying short segments of every newly found long arm. Other 96-edge reference shapes have different completion sets.

The five archived 96-edge parents already known to attain a 191-edge join are donors 30, 49, 59, 69 and 73. Their individual completion sets contain 4, 5, 5, 6 and 6 shapes respectively. None of those five parents belongs to the 98-edge donor’s set of 53. This compares the ability to supply a reusable middle segment with the ability to accept a long opposite arm at an intact endpoint. [Donor identities](../248-rooted-arm-capacity/parents.json) · [Reference incidence](origins.json)

Exactly four reference parents suffice to generate the full set of 63. Donors 15, 69, 99 and 114 give one minimum choice. For each parent the calculation compared its entire set of 68-edge segments with every completed arm. Dropping duplicate rows and rows contained in another row leaves six inclusion-maximal sets. None of their twenty triples covers all 63 shapes. Replacing a smaller row by a containing row cannot decrease coverage, so no three original references suffice. [Incidence and minimum cover](origins.json) · [Independent subset count](origins.py)

## Crossing into the ninth dimension

For a fixed arm of length $a$, a 192-edge join requires an opposite arm with $191-a$ edges. Truncating the far end of that opposite arm gives the same target from any longer join. The 28 previous shapes already had exclusions at both ends. Of the 70 endpoints of the 35 additions, 69 were excluded directly. The remaining endpoint of shape `a97aac9b` has seven legal first steps, all excluded separately. This gives 76 independently checkable contradiction certificates. A previously recorded 191-edge join supplies equality for the full family. Which of the added shapes individually attain 191 remains open. [Endpoint proofs](rooted-proofs.json) · [Full replay](replay-68-192.json) · [Inherited exclusions](../251-eighty-edge-segments/README.md)

A separate construction search placed each of 903 archived donor paths against each new endpoint under all coordinate permutations and examined the fitting consecutive segments. The best segment length at each root ranged from 33 to 44. Further growth produced valid joined paths at all 70 endpoints. Their lengths ranged from 155 to 178 edges. The best uses shape `4274c03c`, with 96 fixed-arm edges, the crossing, and an 81-edge opposite arm. All 15,931 pairs of its 179 vertices were checked for the required adjacencies. [Paths and placement counts](construct-68.json) · [Construction](construct.py)

The global interval remains $191\le a(9)\le231$. The contributor branch audit for 231 passed at revision `a56a972`. Its 230 result still requires an additional premise. [Contributor revision](https://github.com/hironaka-iori/Snake-in-the-box-in-9/commit/a56a972217acd542851578fb185f00ec335099a0) · [Lean receipt](TwoTails252-compile.json) · [Manuscript receipts](manuscripts.json)
