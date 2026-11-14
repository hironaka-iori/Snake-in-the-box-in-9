# Round 218: direct partner queries and necessary inequalities

The target is a 93-edge induced path in the 158-vertex allowed graph of the saved 98-edge Q8 parent, rooted at endpoint 0 or 78. Its other endpoint is free. Only the parent's other 98 vertices are forbidden. A compatible partner would yield $98+93+1=192$ Q9 edges. No such construction was obtained this round.

## Necessary constraints and their proofs

The model selects 94 vertices, with degree one at the prescribed endpoint and one free endpoint, and degree two at all other selected vertices. Degree equations are conditional on selection. Both prescribed vertices have even parity. Consecutive cube edges reverse parity, so a 93-edge partner has 47 vertices of each parity and an odd free endpoint.

PartnerParity218 checks this alternation using the adjacency of an actual induced path of equal-length Boolean words. It then checks the final endpoint parity and both 47-vertex counts. No alternation assumption is substituted for the actual path edges. The numerical integer-to-word interpretation remains distinct from this theorem.

For any simple cycle C and a selection S drawn from an actual induced path, $|S\cap C|\le |C|-1$. If every cycle vertex occurred in the path, choose the last one. Its two distinct cycle neighbours would both occur earlier, and inducedness would force each to be the unique preceding path vertex. This is impossible. Cycle218 checks the noncontainment argument and the counting inequality, reusing the accepted maximum-position argument from round 196. Extra cycle chords are allowed. Two new modules pass with five dependency reports using only the standard foundational axioms.

The selected-degree conditions can still admit separate cycles. The initial model adds 279 cuts at root 0 and 274 at root 78, covering the saved coordinate squares and six-cycles obtained by deleting antipodal vertices of three-faces. Each returned separate cycle would produce another valid cut. A connected solution must also pass direct all-pairs validation in Q8 and Q9. These generic Lean results do not certify numerical cycle extraction, constraint serialization or native solver exhaustion.

## Native outcomes

| Root | Status | Solver seconds | Branches | Conflicts | Dynamic cuts |
|---|---|---:|---:|---:|---:|
|0|UNKNOWN|240.042|12,142,979|8,006,576|0|
|78|UNKNOWN|240.002|12,434,743|8,403,733|0|

UNKNOWN provides neither a construction nor an exclusion. Any INFEASIBLE result has only fixed-parent native-solver scope and requires a separate contradiction certificate. No global upper bound is inferred. The model uses arbitrary partner shapes, with no isometric-copy, fixed-prefix, overlap or replacement restriction. No controlled speed comparison against the old circuit formulation is established.

The first invocation was stopped after a sampled private-memory reading of 590,295,040 bytes, before any model or result artifact was produced. Its sources and receipt remain preserved in data/root-0. A separate invocation limits numerical-library threads to one. The mathematical model and solver parameters are unchanged. The retry's outputs, exact exported models, resource observations and source pins are retained in data/threads1. The independent record audit reconstructs the allowed graphs and compares the exported model with the intended degree, parity and cycle constraints. It does not replay a solver proof.

## Symmetry and next calculation

Rooted graph-colour refinement reaches 158 singleton classes in both allowed graphs: class counts are 8, 95, 155, 158 for root 0 and 8, 95, 153, 158 for root 78. Any root-fixing graph automorphism preserves each refinement step, so these finite calculations leave no nonidentity rooted graph automorphism to exploit. This concerns the two fixed allowed graphs; it does not exclude broader transformations of whole snakes. This is a native finite calculation without a new Lean certificate. No symmetry restriction was imposed on either query.

The conditional degree equation has an exact linear form. Let x and e be Boolean selection and endpoint indicators with e<=x, let d be the available degree, and let s be the selected-neighbour count. Since 0<=s<=d, the implication x=1 => s=2-e is equivalent to

\[
2x-e\le s\le d-(d-2)x-e.
\]

For x=0, e=0 and the bounds reduce to 0<=s<=d. For x=1, both bounds equal 2-e. Signed arithmetic is intended. Relaxing x and e to the interval [0,1] therefore gives a necessary linear relaxation. This short algebraic derivation is written and source-reviewed; no new Lean result or solved linear program is claimed for it this round.

Evaluate the explicit linear relaxation of the fixed-parent partner model at both roots. For each non-root vertex with selection x, endpoint indicator e, ambient degree d and selected-neighbour sum s, replace conditional degree by 2x-e <= s <= d-(d-2)x-e, with 0<=e<=x<=1 and e=0 at other even vertices. Keep root selection/degree1, one free odd endpoint, parity balance and every verified cycle inequality. Maximize total selection after relaxing Boolean variables to [0,1]. An upper bound below94 would exclude this parent target only after an exact rational dual certificate is checked, preferably in Lean. A bound at least94 would show that this relaxation is insufficient, not that a partner exists. Do not repeat an unchanged long query or claim a global Q9 upper bound from a fixed-parent result.

## Maintained research state

The recorded interval remains $191\le a(9)\le233$. Independent full rebuilding of the contributor's233 proof remains pending; contributor b0521e1d and saved final audit b65d30ca are unchanged. The 196 conjecture is unresolved. The prior parent-search states are unchanged: case 22 remains at 1260 cumulative jobs,11,724,609 nodes and eight unfinished regions; 27 of 28 six-coordinate choices remain unresolved.

The goal remains ACTIVE under the user's own-work pause condition. Contributor work alone cannot trigger a pause. No pause is declared and no email is sent; no sending connector is available. Both existing manuscripts compile and exactly match their repository mirrors. Author order and hyperlink settings are preserved. Full-paper review is due at round 220.
