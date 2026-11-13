# Round 197: symmetry classes and quotient constructions

## Main finding

Up to cube conjugacy, there are 20 fixed-point-free involution types in Q8. They have representatives g(y,b)=(h(y),1-b), where h ranges over 20 affine involution types on Q7. A complete census of 6,512 concrete maps h against one published 50-edge Q7 path identifies two placements with just one unwanted contact. Both resist repairs retaining all but at most four seed vertices, according to the native solver. No longer Q9 snake or improved global bound is obtained.

## Classification and separation

Write a cube symmetry as $g(x)=\pi x\oplus a$. It is an involution precisely when $\pi^2=1$ and $\pi a=a$. The permutation therefore has r transposed pairs and fixed coordinates; the translation bits agree within each pair. Conjugation by translation t changes a to $a\oplus t\oplus\pi t$. This removes the common bits on every transposed pair and leaves fixed-coordinate bits unchanged. Relabelling coordinates leaves just r and the number f of flipped fixed coordinates. Conversely, these parameters are invariant under conjugacy, so they classify the involutions.

Every flipped fixed coordinate contributes one to $d_{\mathrm H}(x,g(x))$, and each transposed pair can contribute zero. Thus the minimum displacement is exactly f. The number of concrete maps of type(r,f) in dimension n is

$$\frac{n!}{r!f!(n-2r-f)!}.$$

Choose the 2r moved coordinates, pair them, choose the f flipped fixed coordinates, and assign one common translation bit to each pair. The factors $2^r$ from pairing and translation cancel. This general classification has a written, independently reviewed proof; it has not been encoded in Lean.

For a free Q8 involution, choose a flipped fixed coordinate as the last coordinate. Representatives of its vertex orbits then lie in b=0. The quotient retains ordinary Q7 edges and adds $y\leftrightarrow h(y)$. If h fixes y, that orbit contains an actual edge and cannot be selected. If h(y) is already an ordinary neighbour of y, both endpoints of this double-lift edge cannot be selected. A selected induced quotient path avoiding these obstructions lifts to two separated induced Q8 paths by round 195's lifting argument.

For h of type(r,f), its extension g has minimum displacement f+1. Thus f>=2 eliminates self-contact and double-lift obstructions. Odd f makes the quotient bipartite with ordinary cube parity. Even f gives same-parity matching edges; imposing 25/25 ordinary parity counts on a 50-vertex quotient path would be unjustified.

## Where symmetry can act

A fixed-point-free graph automorphism preserving a nonempty finite induced path must reverse it. Indeed, its restriction is a path automorphism, and fixing either endpoint fixes every vertex by path distance. Reversal would fix a middle vertex when the vertex count is odd, or exchange two adjacent middle vertices when it is even. Consequently, a cube symmetry of minimum displacement at least two cannot preserve a single snake.

It can exchange two separated components. The opposite-face joining paths may break this symmetry in a final Q9 snake. This restriction concerns a specified free symmetry; it does not exclude all symmetries of a snake. Lean checks the central contradiction under an explicit reversal premise. The reduction from a path automorphism to reversal is the written argument above.

## Checked normal form of the earlier symmetry

The round 196 map swaps coordinates 0,3 and 2,4 and translates by 63. Conjugating by translation 5 changes 63 to 34. Delete flipped fixed coordinate 1 from the representative face. The resulting h swaps 0,2 and 1,3 and flips coordinate 4, hence has type(2,1). The Q8 map has type(2,2).

Lean checks 256 conjugacy identities, orbit labels,128 representative identities, the range and involution properties of h, the double-edge criterion, and all 128 times 8 neighbour identities. A double edge occurs exactly when bits 0,2 agree and bits 1,3 agree:32 vertices, hence 16 unordered forbidden pairs. Nine modules check this quotient and one checks the reversal obstruction, with 14 theorem dependency reports. The complete placement census and final solver contradictions are outside these Lean checks.

## Complete placement census for one fixed seed

The input is the 51-vertex Q7 path in round 188's lower-dimensional-seeds.json. Changing h by cube conjugacy while holding this path fixed changes their relative placement. A contiguous seed subpath S lying in one representative face gives separated paired paths exactly when $S\cap h(S)=\varnothing$. It uses no additional matching steps.

| r | f | Maps | Fewest full-seed contacts | Longest direct subpath, edges |
|---:|---:|---:|---:|---:|
|0|0|1|51|none|
|0|1|7|2|24|
|0|2|21|3|36|
|0|3|35|3|35|
|0|4|35|2|33|
|0|5|21|5|31|
|0|6|7|8|28|
|0|7|1|6|35|
|1|0|42|26|12|
|1|1|210|1|42|
|1|2|420|2|38|
|1|3|420|3|36|
|1|4|210|5|36|
|1|5|42|4|35|
|2|0|420|13|17|
|2|1|1260|2|38|
|2|2|1260|1|45|
|2|3|420|2|39|
|3|0|840|9|26|
|3|1|840|3|38|

The direct maximum is two 45-edge Q8 paths,92 vertices total. This remains below the saved 47-edge pairs obtained by a different construction. The census concerns one Q7 snake and its contiguous subpaths; it does not exhaust arbitrary quotient paths or all optimal Q7 snakes.

The old type(2,1) has five placements with exactly two contacts. The only one-contact cases across all types are row 252, type(1,1), with contact(38,43), and row 4147, type(2,2), with contact(4,38). Indices are zero-based. These close cycles of length 6 and 35 respectively. In row 4147, positions 5 through 50 give the 46-vertex direct subpath.

## Repairs and evidence

The repair model selects an induced path in the full quotient, with both endpoints free, fixed vertex count, bounded seed omissions and forbidden double-lift pairs. Its initial degree constraints can permit disjoint cycles. Every recorded dynamic cycle cut must be included when reproducing the terminal model.

All five two-contact type(2,1) cases are INFEASIBLE for 50 vertices with at most four omissions, each in about 1.2--2.2 seconds. The two one-contact cases are also INFEASIBLE: row 252 in 6.532 seconds after three cycle cuts, and row 4147 in 6.875 seconds after one. Thus each of these seven specific placements requires at least five omitted seed vertices and four added vertices for a 50-vertex safe quotient path. The seed has a chord in the quotient, so this is a repair restriction relative to a vertex set, not a comparison between two valid quotient snakes.

Row 4147 with eight omissions is UNKNOWN for 50 vertices after 120.016 seconds. A49-vertex probe with eight omissions is also UNKNOWN after 90.031 seconds. Neither timeout excludes a solution. The solver exclusions have no Lean contradiction certificates. The new dynamic cycle cuts are separate from the three checked in round 196.

Even without the solver, deleting one seed vertex cannot repair either one-contact case to 50 vertices: deleting a contact endpoint disconnects the path, while deleting another vertex cannot lower both degree-three contact endpoints because their ordinary neighbour sets are disjoint.

## Next step

Prioritize Q8 type(2,3), represented by row 4147's h of type(2,2). Partner distance at least three removes double-lift constraints. Split the search according to whether the contact(4,38) is retained as a path edge. If retained, omit at least one ordinary neighbour of each contact endpoint, giving four initial choices, and reconnect the remaining chains. If omitted, repair the break. Keeping both original seed endpoints requires an odd number of matching steps because ordinary Q7 edges change parity and matching edges preserve it.

An ordered path search can maintain connectivity and avoid the degree model's disjoint cycles. Endpoint compatibility must remain part of the objective: a 100-vertex paired face needs 95 opposite-face vertices for 194 edges, or 93 for 192, with three opposite components and four crossings. Smaller pairs and other symmetry types remain useful if they permit better completion. No success probability is asserted.

The contributor branch at 351bca82 reports 2,991 of 3,127 local certificates built. It was neither merged nor independently rebuilt. Upper-bound status is unchanged. Research remains active. Sources, native records, exact models and proof receipts are retained in this milestone; PRIOR_ART.md records the limited literature refresh and makes no novelty claim.
