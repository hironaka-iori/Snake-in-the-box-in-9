# Boundary contraction and the next construction search

Status: source prepared only. No compiler, solver, native worker or software tests were run. Existing accepted round-226 sources were left unchanged. The numerical shorter-family exclusion remains an explicit premise.

`BoundaryContraction226.lean` uses ordinary vertex maps (p,q:\mathbb N\to V), with agreement restricted to indices at most (n). It introduces no definitions. A finite indexed path may be represented by such a map on its valid indices; values beyond (n) do not enter the agreement conclusion.

The first exported theorem derives agreement outside shortened intervals. If (q(a+1)=p(a+1)), replacing ((a,b)) by ((a+1,b)) removes only the index (a+1) from its open interior, and equality at that index supplies the missing agreement. If (q(b-1)=p(b-1)), the analogous right contraction removes only (b-1). Applying the argument to both blocks gives one of the four left/right contraction combinations, for the identical full candidate (q).

The second theorem proves that either contraction preserves interval containment and reduces the edge length by exactly one, provided the original interval has at least two edges. Thus 44-edge intervals become 43-edge intervals. Ordering and separation of two original intervals persist because the contracted intervals are contained in them. The candidate's path, endpoint, total length and crossing properties are unchanged because the vertex map itself is unchanged.

The third theorem is the conditional contrapositive. If the same candidate is excluded in all four contracted contexts, then

\[
\bigl(q(a+1)\ne p(a+1)\ \land\ q(b-1)\ne p(b-1)\bigr)
\quad\lor\quad
\bigl(q(c+1)\ne p(c+1)\ \land\ q(d-1)\ne p(d-1)\bigr).
\]

Consequently a successful candidate escaping an excluded family of shorter replacements must change both boundary-adjacent vertices of at least one block. This is a necessary condition for the next construction search; it does not establish the existence of such a candidate.

The numerical bridge must identify each applicable contracted context in the actually excluded family, or in a justified inherited family, with the same original path, final candidate target and other restrictions. Width alone does not establish that membership. The theorem's `shorter_excluded` premise is already specialized to these fixed candidate conditions and does not claim a general upper bound or certify the solver transcripts.

The module imports only `Std` and requests three axiom reports: `contract_two_intervals`, `contracted_interval`, and `escape_requires_two_boundary_changes`. The agreement derivation is part of the proof; shrink-closure is not assumed. Compilation and the concrete shorter-family interpretation remain pending.
