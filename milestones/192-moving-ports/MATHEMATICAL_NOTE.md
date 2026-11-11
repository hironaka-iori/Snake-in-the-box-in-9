# Round 192: moving endpoints and coordinated square substitutions

The user explicitly resumed the goal after the round191 pause. This round leaves the goal active.

## General accounting

Let P and Q be induced paths of positive length, with Q longer by delta edges. Let D, A and C be the omitted, added and common vertex sets. Put r=|D|. Let d count old endpoints in D and a count new endpoints in A. Then

\[
|A|=r+\delta,\qquad e(A)+a=e(D)+\delta+d,
\]
\[
e(A,C)+d=e(D,C)+a.
\]

The added-component count plus d equals the deleted-component count plus a. The degree sums are 2r-d and 2(r+delta)-a. Substitute them into the total-edge difference, then use vertex count minus edge count for the two induced path forests. Positive path length is required for endpoints to have degree one; singleton paths are outside this statement.

At a retained vertex, the added-neighbour count plus its new-endpoint indicator equals the deleted-neighbour count plus its old-endpoint indicator. In particular, retaining an old endpoint as internal requires one extra added neighbour. The finite edge/degree and attachment implications pass Lean under their explicit premises. The generic path-to-count integration remains written.

For191 to192 edges, the colour counts change from(96,96) to(97,96) or(96,97). Therefore at least one global endpoint must change. Moving only the middle or crossing vertices while retaining both global endpoints cannot give an odd edge gain. Alternating sequence counts for this change pass Lean.

## Joint replacement search

The selected seed is the normalized bank25 witness: a191-edge path with the common95-edge middle. Its two-crossing coordinate is moved to coordinate8. Both global endpoints, all selected vertices and all crossing vertices may vary in the new model. It selects193 vertices, imposes two degree-one endpoints, degree two at every other selected vertex, colour counts, the endpoint-corrected edge identity and4608 square exclusions. Longer disconnected cycle components remain possible initially, so this is a relaxation containing every desired induced path.

| Query | Result | Seconds |
| --- | --- | --- |
| At most4 omissions, exactly2 coordinate8 crossings | INFEASIBLE | 27.578 |
| At most4 omissions, unrestricted crossing counts | INFEASIBLE | 30.907 |
| At most6 omissions, exactly2 coordinate8 crossings | UNKNOWN | 120.078 |

Hence a192-edge path within this seed's vertex-set neighbourhood requires at least5 omissions and6 additions computationally. This is a different problem from the fixed95-to97 middle replacement, whose previous lower restriction is8 omissions. Neither solver exclusion has a Lean contradiction certificate. The six-omission timeout supplies no exclusion.

## A complete restricted transformation search

At internal position i of a displayed191-edge path, the alternate square corner is

\[
w_i=v_{i-1}\oplus v_i\oplus v_{i+1}.
\]

Choose either the original vertex or this fixed alternate corner at each of the190 internal positions. Keep positions0 and191 unchanged, then seek one new vertex at either end. This is one simultaneous batch; alternate corners are computed from the original path.

Every invalid original/alternate pair produces an implication between substitution choices. Every invalid alternate/alternate pair forbids selecting that pair. An extension vertex forces substitution wherever the original vertex conflicts with it, and forbids substitution wherever the alternate vertex conflicts. Start from the required choices and close under implications. A forced fixed endpoint, forbidden choice, or forbidden pair disproves feasibility. Otherwise the closure itself is a satisfying choice, with all other substitutions false. This proves completeness of the native method for this specified family.

All2358 endpoint candidates across131 saved witnesses are excluded. The separate single-square census has24890 candidates and142 valid moves in Q9, all equivalent to existing bank members. The displayed Q7 and Q8 optimal seeds have no valid single-square move. Of352 pairs of one-square slides at two-crossing coordinates, none is valid.

Forcing one internal substitution and taking its least implication closure produces147 distinct valid rooted closures across the bank:142 single substitutions,4 double substitutions and1 triple substitution. All147 results belong to existing canonical bank classes. None of these147 closures moves the crossing positions of a coordinate crossed exactly twice. These are rooted-closure statements; the147 cases do not enumerate every valid simultaneous substitution set or every compatible union of closures. The full endpoint-extension exclusion is nevertheless complete, because each extension query computes its own entire forced closure.

Canonicalization uses translation, coordinate permutation and reversal. No classification of all191-edge snakes or novelty claim is made. Successive batches with recomputed corners, arbitrary replacement vertices and reordered path segments remain outside the exclusion.

## Concrete geometric Lean result

All18 endpoint candidates of the normalized bank25 seed pass Lean, with a combined theorem covering either end and any of the9 directions. The theorem permits an arbitrary Boolean choice at each internal position. Its premises require nonconsecutive selected vertices to be distinct and nonadjacent, and the proposed new endpoint to be separate from every old position except the attachment endpoint. These conditions are necessary for an induced extension. Consecutive-edge premises are unnecessary for the contradiction; omitting them enlarges the candidate family.

The proof checks the actual numerical alternate-corner coordinates using the Lean kernel. Short implication chains force either an unchanged endpoint to be substituted or a forbidden alternate vertex to be selected. These certificates are geometric checks for this specific seed, rather than merely replaying an unsupported solver status. The full131-seed census remains native.

In total23 new modules pass with30 dependency reports. One aggregate proof attempt failed because a direction-case hypothesis shadowed an endpoint hypothesis and the reduction depth was too small; its exact source and log remain saved. The corrected aggregate passes. A startup gate temporarily stopped the batch before case12 when free memory was1062440960 bytes, below1GiB. It resumed after1256591360 bytes became available. No compiler was launched at the failed startup gate, and the resource limits were not changed.

The first concrete-certificate generator assertion caught extension directions still using the raw coordinate labels. Raw coordinate5 is moved to8, while raw6,7,8 become5,6,7. The exact vertex-by-vertex coordinate map is checked before the final cases are generated. Every final numeric geometric claim is then checked by Lean.

## Frontier

No longer Q9 snake or new global upper bound was found. The strongest new checked construction restriction is the selected witness's inability to grow through any simultaneous fixed-square substitution and endpoint extension. The new accounting also describes endpoint changes correctly in broader searches.

The next constructive move should permit vertices outside the alternate-square choices. A concrete finite next step is to enumerate reorderings of three or four consecutive transition directions, preserve each block's endpoints, and check the whole path for chords and endpoint growth. Such reroutings can change the two internal vertices together in ways unavailable to the square-choice model. Their effects on the rare crossing coordinate can be recorded explicitly. This is a proposed search, with no success prediction or claim that it covers arbitrary paths.

The upper-bound project is unchanged: archived235 awaits complete independent rebuilding;233 and234 retain local/graph premises. Round187 has93/98 clause batches and11904/12424 clauses checked; the critical contradiction and actual-snake transfer remain pending. The round188 direct Q8 all-pairs Lean recheck remains pending. Full manuscript consistency review was completed190; the next scheduled review is200.

Contributor branch research/unconditional-241 advanced to b2f85574241bd8d9aca499440b9bc0f3b4c0def0, adding36 production records. The diff is archived. This was not merged or independently rebuilt and establishes no changed global claim here.
