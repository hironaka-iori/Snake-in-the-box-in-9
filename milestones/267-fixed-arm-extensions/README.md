# Round 267 · Rebuilding one arm when its partner contains a published interval

**The longest one-crossing snake whose arm contains any of five specified 94-edge intervals has exactly 191 edges.** The five intervals are the shorter arms of the 25 archived one-crossing 191-edge examples. The interval can lie anywhere in either arm. Both choices of crossing endpoint are covered for every containing arm. The opposite arm is unrestricted. [A 191-edge attaining path](attaining-191.json) · [Coverage and replay](summary.json)

## Which fixed arms can contain the interval?

| Length of containing arm | Shapes up to symmetry | Rooted cases | Opposite arm needed to reach 192 |
|---:|---:|---:|---:|
| 94 | 5 | 10 | 97 |
| 95 | 11 | 22 | 96 |
| 96 | 2 | 4 | 95 |

A longer containing arm would arise by successive one-edge additions at the two free ends of the interval. The complete eight-dimensional enumeration stops at 96. An independent enumeration produced the same 18 shapes. For a fixed containing arm, shortening a sufficiently long partner at its free end gives the exact target of 192. [Eight-dimensional extension catalogue](../266-rebuilding-one-arm/windows.json) · [Independent enumeration](../266-rebuilding-one-arm/verify.py)

The ten cases of length 94 have checked exclusions from Round 266. For eleven of the 22 cases of length 95, the crossing end begins with a full 94-edge reference. The only possible 96-edge partners for that prefix are its five published partners, or there are none if the crossing is at the opposite endpoint. Every candidate collides with the added site. Whole-complement or grouped certificates exclude the other eleven crossings. The two 96-edge shapes already belong to the earlier family of arms retaining a 68-edge reference interval. This covers all 26 rooted cases in the two longer rows. [Length-94 census](../266-rebuilding-one-arm/summary.json) · [Root identifiers and inherited exclusions](cases.json) · [Earlier 68-edge family](../252-shorter-reference-segments/README.md)

## Searching beyond the five intervals

The published 190-edge archive supplies 62 shapes of 95-edge arms. Their 124 crossing endpoints and the 26 endpoints of the longer containing arms give 148 distinct rooted cases, with two in common. The arm and crossing endpoint remain fixed in each construction. [Fixed arms and known partners](cases.json)

The unrestricted 192-edge search excluded all 148 selected endpoint cases. Retaining any of the 62 archived 95-edge shapes as a whole arm caps the join at 191 edges at either crossing endpoint. These shapes occur as 95-edge arms in 329 archived 190-edge snakes. The final replay checked 85 contradiction certificates, including 42 for prescribed first steps. [Exact endpoint coverage and certificate counts](summary.json)

A candidate 95-edge partner gives 192 when the fixed arm has length 96. When the fixed arm has length 95, reaching 192 requires a 96-edge partner, whose first 95 edges also give a necessary construction. Several fixed parents can be aligned in the same coordinates. A partner must avoid their common blocked sites. To require compatibility with at least one complete parent, a Boolean choice selects that parent and forbids its remaining sites. A contradiction without the extra choice already excludes every member of the group. A positive path is checked against the actual full parent. [Grouped searches](families.json) · [Direct searches at 192](direct-192.json)

An earlier certified set of blocked vertices must be met by every rooted 95-edge path. After a coordinate permutation, its members outside the current common blocker set therefore form a mandatory disjunction. Conversely, a set of optional vertices that intersects the extra blockers of every parent cannot all be selected. The certificates include both types of conditions when applicable. The replay reconstructs the permutations, the parent intersections and the resulting clauses. [Transported blockers](cuts.json) · [Strengthened queries](strengthened.json)

For a 96-edge partner whose first edge is $0\to s$, remove the original root and its neighbours other than $s$, as well as the nonzero sites of the fixed parent. Translate $s$ to zero. A rooted 95-edge induced path in this domain gives the complete partner by undoing the translation and prepending the original zero. This correspondence covers every partner with that first step and prevents an extra adjacency to zero. [First-step certificates](suffixes.json) · [Formula and geometry replay](verification.py)

## Constructing the opposite arm by local changes

At 63 fixed endpoints the archive gives 329 labelled 94-edge starting partners. Allow the opposite arm to replace at most one occupied site while keeping an induced path from zero. Then extend the free end by one edge, keep it, or delete it. The resulting partner must avoid the fixed parent except at zero. Both steps belong to one move. Each move changes only the opposite arm.

| Minimum permitted partner length | Reachable labelled parent–partner pairs | Longest partner | Longest join |
|---:|---:|---:|---:|
| 92 | 1,394 | 94 | 190 |
| 88 | 102,669 | 94 | 190 |

At the lower threshold there are 798,897 legal ordered moves. The 329 states of partner length 94 are exactly the starts. Thus any improvement using these moves with the same fixed parents and starts must pass through a partner of at most 87 edges, or a join of at most 183. An independent program deletes and inserts a site, reconstructs its order from the induced adjacency graph, and checks the resulting endpoint edits. Its state hashes and move counts are compared separately at each root. [Threshold 88](single-88.json) · [Threshold 92](single-92.json) · [Independent graph traversal](ReplayArm.cs) · [Replay results](construction-audit.json)

A second construction generated opposite arms before selecting their cube placements. From 418 distinct eight-dimensional starts of length at least 95, allow the same operation at either end and require at least 95 edges after each move. This closes at 2,760 shapes, with 2,318 of length 95, 434 of length 96, seven of length 97 and one of length 98. The starts included 261 of the 96-edge shapes. Thus the operation supplied another 173 shapes of the target length within this catalogue. An independent enumeration checked both closure and reachability from the starts. [Generation and lengths](donors.json) · [Paths and predecessors](donor-paths.json.gz)

Every directed segment of a suitable length in the resulting collection was placed under all $8!$ coordinate permutations at the fixed roots. Compared with the starting donors, this improved placements at 65 endpoints, by up to 13 edges. The largest join found has 191 edges and matches the published archive. The independent target-length check excluded every placement at 192 from this donor collection. Shortening the partner at its free end covers longer donors. [Placements and explicit joins](placements.json) · [Independent target-length enumeration](replay_constructions.py)

The global interval remains $191\leq a(9)\leq230$. These fixed-arm results concern a single crossing. The contributor’s saved upper-bound audit passed. Revision `dc94edd810` adds a progress report on replaying certificates in stages. The upper-bound theorem and its audit match the previously reviewed revision. An independent full rebuild remains pending. [Contributor revision](https://github.com/hironaka-iori/Snake-in-the-box-in-9/commit/dc94edd8109ae6046389ee30fedc8808bd1c2d97) · [Upper-bound evidence](../264-distant-component/contributor.json) · [Manuscripts](manuscripts.json) · [Guarded execution records](runs/)
