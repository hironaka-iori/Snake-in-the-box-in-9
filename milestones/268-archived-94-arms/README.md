# Round 268 · Rebuilding the partner of an archived 94-edge arm

Of the 329 archived one-crossing 190-edge examples whose arms have 94 and 95 edges, 35 use one of the five shorter-arm shapes studied in Round 266. The other 294 examples supply 63 further shapes for the 94-edge arm. Both endpoints of every one of these 63 shapes were considered as possible crossings. A 97-edge partner would give a 192-edge snake. A 96-edge partner would give 191. [Archived arms and labelled starting partners](../266-rebuilding-one-arm/parents.json) · [Certified endpoint coverage](summary.json)

**Keeping any of these 63 whole arms gives at most 191 edges, whichever endpoint is used for the crossing.** All 126 endpoint cases exclude a 97-edge partner. The construction search attained 190. The 96-edge partner search resolved 54 of the 63 published crossing endpoints, each with exact maximum 190. [Explicit 190-edge path](example-190.json) · [Whole-root queries at 192](queries-97.json) · [First-step queries at 192](steps-97.json) · [Construction search](CONSTRUCTIONS.md)

| Holding the 94-edge arm at the archived crossing | Archived 190-edge examples |
|---|---:|
| Maximum 191, with five known replacements for the opposite arm | 35 |
| Maximum 190 | 273 |
| Attained 190, maximum at most 191 | 21 |

The first row follows from the five record-arm censuses of Round 266. At each of those fixed endpoints, each of seven archived 190-edge examples can use any of the five archived 96-edge partners. The second and third rows come from this round. The 21 examples with a remaining gap occur at nine rooted parents. [Explicit replacement arms and source examples](known-upgrades.json) · [Whole-root queries at 191](queries-96.json) · [First-step queries at 191](steps-96.json)

## Exact partner search

Translate the crossing to zero in both eight-dimensional faces. A candidate partner must be an induced path from zero whose other vertices avoid the fixed arm. Any sufficiently long partner can be shortened at its free end to the target length.

An axis permutation puts several fixed parents in common coordinates. The 126 endpoint cases form 38 groups, each sharing 88 to 94 forbidden vertices. A Boolean variable for each parent allows the search to select any parent in the group. Selecting a parent forbids every occupied site of that parent other than the common root. This gives one existence question for the entire group, while preserving the full restrictions of the selected parent. [Groups, permutations and common blocked sites](groups.json) · [Search and Boolean encoding](search.py)

For 97 edges the partner uses 49 vertices of each parity. For 96 edges it uses 49 even vertices and 48 odd vertices. Zero and one other vertex are endpoints. All other selected sites have induced degree two. A disconnected arrangement contains a cycle whose complete vertex set cannot belong to an induced path. The formula records any excluded cycles. The checker reconstructs the coordinate maps and all clauses before replaying the contradiction certificates. [Base encoding](../266-rebuilding-one-arm/rebuild.py) · [Independent replay](audit.py)

### Locating the second endpoint from the parity counts

The sum of the selected degrees on the even vertices equals the sum on the odd vertices. Each sum counts every edge once. This removes the need to choose the second endpoint explicitly.

For 97 edges, give the even root degree one and all 48 other selected even vertices degree two. Their degree sum is 97. The 49 selected odd vertices can each have degree at most two. They have total capacity 98, so exactly one has degree one and the rest have degree two. For 96 edges, give each of the 48 selected odd vertices degree two. The 49 even vertices then have degree sum 96 against capacity 98. The root accounts for one unit of deficit. Exactly one other even vertex has degree one. In both cases, every connected selection is the desired induced path. [Parity-based formula](deficit.py)

### Fixing the first edge

If the partner starts with $0\to s$, remove zero and all its neighbours other than $s$. The remaining path starts at $s$ and avoids the fixed parent. Translation by $s$ sends this problem back to a path rooted at zero, with length smaller by one. Undo the translation and prepend the original zero to recover the complete partner. A coordinate permutation can transfer a previously checked 96-edge exclusion whenever its forbidden sites are contained in the new forbidden sites. This transferred two of the 882 possible labelled first steps across the 126 fixed roots. [First-edge search](split.py) · [Transport from Round 267](transport.py) · [Source roots and coordinate permutations](transfers.json)

## Scope

The fixed arms are taken from the specified finite archive. The partner ranges over the entire opposite face. The replay covers 88 contradiction certificates across the two target lengths. Every 192-edge case is covered, including those which required a split after an initial time limit. The unresolved 191-edge cases are listed by parent and first step in the replay summary. The global maximum in the nine-cube remains open. [Certificate files](proofs/) · [Execution receipts](runs/)
