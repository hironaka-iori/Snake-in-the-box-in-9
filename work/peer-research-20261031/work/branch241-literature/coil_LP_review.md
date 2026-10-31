# Coil LP review and independently proved Q9 transfers

Source: Kevin M. Byrnes, Eric T. Harley and Florin Spinu, [Linear Programming Upper Bounds for the Coil-in-the-Box Problem, arXiv2610.36461v1](https://arxiv.org/html/2610.36461v1), submitted2026-10-27. [Abstract](https://arxiv.org/abs/2610.36461). The primary agent downloaded the25-page PDF and extracted text under papers/coil_lp_2026.pdf and papers/coil_lp_2026.txt. I read the accessible primary full text, including appendices and the dual-feasibility argument. My separate shell download was denied socket access; I did not bypass it.

## Paper-specific applicability audit

The standing domain is n>=13 and a maximum coil. Its LP combines complement-degree moments, high-degree-neighbor incidence and heavy-segment inequalities. The deletion of y_n depends on a maximum-coil property. AppendixA uses connectedness and a length lower bound to reject a closed configuration; its companion estimate also depends on dimension. Heavy-segment packing and admissible-pair multiplicity need the stated coil machinery. They are not proved here for snakes or disconnected cycle unions. The analytic dual certificates and their numerical formulas therefore cannot be imported at n9. These statements concern the hypotheses of the cited paper, not an assertion that every inequality fails outside them.

The following results are independent derivations and explicit checks made for this project, rather than a paraphrase of additional paper text.

## A direct n9 dual failure

Evaluate the polynomial R=n²−14n+32 at9: R=−13. The first proposed dual has unscaled slack(n−1)R at y_(n−1), giving−104, while its normalizing denominator is positive. Thus that dual is actually infeasible at n9. Also M=floor(3n/4)=6 equals n−3, collapsing two supposedly separate support positions. Blind substitution produces4571136/18535, but this is NOT a certified Q9 bound. The failure is stronger than merely lacking an advertised theorem at9.

## Explicit counterexample to transporting y_n=0

Let e_i=2^i for i0…8. Select the18 vertices in cyclic order

    e0,e0+e1,e1,e1+e2,...,e8,e8+e0.

Every selected pair vertex is adjacent to exactly its two incident selected unit vertices. No other selected adjacency exists, so this is a genuine induced C18. The unselected origin has all9 cube neighbors selected. Therefore y9=1. Delete the final pair vertex e8+e0: the remaining17 vertices form a genuine induced path and still have y9=1. Both lists and all unordered pair checks are in coil_transfer_checks.json.

Consequently y9 cannot be removed from a complement-degree LP for arbitrary snakes, arbitrary coils, or unions of coils. Maximum-coil assumptions must not silently become local-model axioms.

## Portable counting identities with the endpoint/component correction

Let S induce a linear forest in Q_n, n>=2. Write v=|S|, c=number of components including isolated points, i=number of isolated points, and y_j=number of outside vertices with j selected neighbors. Let F0 count empty coordinate squares; F1 count squares with three selected corners; Fo count squares with exactly two opposite selected corners; Fs count singleton squares.

Since |E(S)|=v−c, edge double counting gives

    sum_j j*y_j = (n−2)v+2c.

The number of degree-two selected vertices is v−2c+i. Each corresponds uniquely to a three-selected-corner square, because a forest contains no selected four-cycle. Hence F1=v−2c+i.

Two square incidences valid for arbitrary selected sets are

    B := sum_j C(j,2)y_j = F1+2Fo,
    sum_j C(n−j,2)y_j = Fs+4F0.

A third arbitrary-set identity is

    Fs+2Fo = sum_{x in S} C(n−deg_S(x),2).

To prove it, choose two coordinate directions at x in which neither neighbor is selected. The opposite corner is either unselected, yielding a singleton square counted once, or selected, yielding an opposite pair counted twice overall. For a linear forest, this sum is

    C(n−2,2)v +2(n−2)c+i.

Substitute Fs=sum C(n−deg,2)+F1−B, expand C(n−j,2), and use the outside vertex count2^n−v and the edge identity. Straight simplification yields the exact identity

    B=(n²−3n+3)v−n(n−1)2^(n−2)+2(n−2)c+i+2F0.

At n9 this becomes B=57v−9216+14c+i+2F0. For one nontrivial snake, c1,i0, so

    B=57v−9202+2F0.

The same formula holds for unions of paths and induced cycles of length at least6 if c denotes only the path components. Therefore this moment identity itself cannot distinguish a single path from a path plus long cycles. For arbitrary maximum-degree-two sets, including selected C4 components, add−2 times their number to its right-hand side.

## A quantitative empty-square/undominated-vertex inequality

For ANY selected set of maximum induced degree2, let i count isolated selected vertices. Then

    y0 <=4F0+i.

Proof. Call an outside undominated vertex x bad if no empty coordinate square contains x. As x and all its neighbors are unselected, every distance-two point must then be selected. A distance-three point cannot be selected: it would have three selected neighbors. Every distance-two selected point is consequently isolated. Each bad x is at distance two from all C(n,2) such isolated points; each isolated point is at distance two from at most C(n,2) bad x. Thus there are at most i bad vertices. Every remaining undominated vertex lies on an empty square, and each empty square has only four corners, giving the result.

For genuine nontrivial snakes and unions of cycles, i0 gives y0<=4F0. This requires neither maximum-coil optimality nor n>=13. It strengthens a mere positivity obstruction, but it does not rule out actual long-cycle unions by itself. No novelty relative to the literature is asserted.

## Verified moment-LP obstruction at236 vertices

The integer vector v236,F0=0,T954,y5=122,y6=34,y7=120, with other y_j zero, gives respectively

    sum y=276, sum j*y=1654, sum C(j,2)y=4250.

These match the corrected snake identities. It also satisfies y0<=4F0, T+2F0=9214−35v, and the additional TEST inequality T>=4v+6 because954>=950. Even the candidate high-degree expression4y7−y6=446 is at most2v=472. This proves only that these moment constraints cannot exclude236 vertices. It is not a geometric realization or a counterexample to a true snake upper bound.

## Independent cutset boundary audit

For a nontrivial induced path and any U, summing selected degrees inside U gives

    selected_cut(U)+global_endpoints(U)=2*components(S intersect U).

Thus a selected root in U implies a lower bound2. To encode this locally, all crossing selected edges and the correct global endpoint flags must be represented. N[U] subset of the variable domain is a sufficient check; the existing interior endpoint encoding then has all9 neighbors available.

Without it, a real snake may be falsely removed. The path[0,1,3,7,15,31,63] is induced and contains the window[0,1,3]. In B4(1), choose U={31}. Its true selected crossing edges go to15 and63, but63 lies outside the ball. Truncation counts only one edge while31 is not a global endpoint:1+0<2. The proposed cut is therefore invalid unless the boundary check succeeds.

## Reproduction and limits

check_coil_transfer.py exhaustively checks15,810 maximum-degree-two subsets of Q3/Q4. All corrected moment identities (including the C4 correction) and y0 budgets pass. It also validates the C18/path17 counterexamples, the boundary counterexample and the integer moment vector. These computations supplement the independent proofs above. They establish no improved numerical a(9) bound and no new Lean bridge.
