# Complete donors aligned through internal anchors

Checkpoint: 20 October 2026. No improved snake witness was found.
Following the user's updated direction, the construction work now pursues
any verified improvement above 191 edges; 196 remains an unproved numerical
conjecture, without exclusive priority.

## Construction and census

The complete 191-edge source witness is transformed by the same isometry
as milestone 20's paired 190-edge prefix. The resulting donor begins at 41,
has vertex 67 at position 190, and ends at 83. Lean checks these identities
and the equality of its 190-edge prefix with the earlier paired witness.

The recipient is the milestone 19 186-edge path, oriented from 41 to 67.
Donor anchor pairs are (0,190), (6,186), (26,166), and (46,146).
The first is a control; the other three are internal pairs. Each pair has
Hamming distance four. For each pair, all 5,760 coordinate isometries mapping
the anchor set to {41,67}, with either orientation, are enumerated. The
donor endpoints need not match the recipient endpoints.

The search considers both:

- replacing one recipient interval by a donor interval with matching anchors;
- retaining either recipient end and replacing the other end by a donor tail,
  in either donor orientation.

Every candidate with at least 192 edges is tested. There were 27,374,032
interior candidates and 3,204,120 tail candidates, before rejecting repeated
vertices and cross-adjacencies. None passed. These counts include candidates
generated more than once by different alignments; they are not distinct
isomorphism classes. This is ordinary finite computation in a specified
family, not a Lean-certified exclusion of longer snakes.

An independent direct-pair audit checks all candidates in sixteen sampled
alignments: 23,785 rejections. Five saved simple 196-edge walks have
25, 26, 45, 31 and 24 chords respectively. They were retained by the number
of conflicting recipient vertices, so 24 is only the smallest chord count
among the saved candidates. None is a snake. They are less attractive for
small repairs than the earlier six-chord candidates.

## Evidence and reproduction

`lean/FullDonor.lean` has four successful audits, using only propext,
Classical.choice and Quot.sound. Its dependency `PairedSeed.lean` was rebuilt,
with ten successful audits. The first donor compile hit the default recursion
limit; increasing that limit allowed kernel evaluation to complete. No
`sorry`, new axiom or native evaluation was added.

Run from the repository root:

```sh
python milestones/22-internal-anchor-donors/scripts/search.py
```

On the established Windows Lean/mathlib installation:

```powershell
.\milestones\22-internal-anchor-donors\scripts\check_lean.ps1
```

That script also checks milestone 23's target and preprocessing lemmas.
Then run:

```sh
python milestones/22-internal-anchor-donors/scripts/verify.py
```

The verifier checks source hashes, all enumerated coordinate permutations,
the sampled direct census, every saved defect list and the Lean receipts.
It does not certify the full enumeration in Lean.

## Collaborator update and next direction

Main remained at ad5a7862 at the initial fetch. The collaborator branch
`research/unconditional-241` advanced to 7d7ee17b, adding shorter-certificate
generation and disk-frugal replay handling. These tooling changes introduce
no new bound adopted in this round. The current interval remains
191 <= a(9) <= 238, with the previously recorded independent-rebuild limitation.

Milestone 23 proceeds to parity-compatible local searches at 193 edges and
compares 192/193 in larger regions. There is no reason to require a successful
construction to have exactly 196 edges.
