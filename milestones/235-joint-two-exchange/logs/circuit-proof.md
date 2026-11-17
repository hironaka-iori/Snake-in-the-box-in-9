Compilation update: all four reports passed the guarded Lean compiler. See data/CircuitPath235-audit.json. Preparation-time status below is historical.

# From a selected-vertex circuit to an induced path

CircuitPath235.lean is prepared source with four intended axiom reports. It has not been compiled. No compiler, solver, or tests were run. The accepted LayerJoining path structure is reused. The milestone-199 optional-vertex circuit source and milestone-219 signed Boolean-product theorem were inspected. The new natural-number helper specializes the latter arithmetic pattern to the sum of the two directed arc indicators without importing the unrelated weighted-certificate development.

## Edge constraints

For a cube edge joining vertices with Boolean selections $x,y$, let $f,b$ be its nonnegative directional indicators. The three model inequalities are

\[
f+b\leq x,\qquad f+b\leq y,\qquad f+b\geq x+y-1.
\]

The proposed boolean_edge_constraints theorem proves their equivalence to $f+b=xy$ for natural $x,y\leq1$. Its lower bound uses natural subtraction; the zero-product cases still give the same encoding. The upper bounds already imply $f,b\leq1$, so no separate Boolean assumption on them is needed for this equivalence.

When both endpoints are selected, $f+b=1$. The one_direction theorem gives exactly the alternatives $(f,b)=(1,0)$ or $(0,1)$. If either endpoint is unselected, both indicators are zero. Thus every adjacent selected pair must be represented by one directed arc. In particular, these constraints exclude a selected chord once the arcs are constrained to follow a single path order.

## Ordered-arc bridge

The generic path constructor takes a vertex map on positions $0,\ldots,m$ and an arc relation. Its three substantive premises are:

1. Every arc is supported on an ambient adjacency.
2. Every ambient adjacency between distinct vertices appearing in the order is covered by one of the two arc directions.
3. Between ordered positions $i,j$, an arc exists exactly when $j=i+1$.

The third premise is a statement about directed arcs and their extracted order, not an assumption that ambient adjacency already equals path adjacency.

Injectivity follows from the arc condition. Suppose an earlier position $i$ repeats the vertex at a later position $j$. The earlier position is not the last, so it has an arc to position $i+1$. Equality of the two vertices gives the same outgoing arc from position $j$. The exact successor condition then gives $j+1=i+1$, contradicting the strict order. The proposed successor_arcs_injective theorem proves this, including the singleton-path case.

For inducedness, take $i<j$. If the two vertices are ambient-adjacent, coverage gives a forward or backward arc. A forward arc gives $j=i+1$. A backward arc would give $i=j+1$, which is impossible. Conversely, successive positions have an arc and hence ambient adjacency by support. The path_of_ordered_arcs definition supplies both required fields of an actual indexed InducedPath, deriving injectivity rather than assuming it.

No symmetry assumption is required by this abstract ordered statement. The cube instantiation has its usual symmetric, irreflexive adjacency.

## Solver extraction and literal inputs remain separate

For the intended native model, unselected vertices have their self-loops selected; selected vertices do not. One mandatory dummy belongs to the nontrivial circuit. The single-circuit constraint must place every selected cube vertex in that circuit and exclude any additional disjoint nontrivial cycle. Removing the dummy, and following the remaining successor arcs, supplies the required order. Arc support concerns cube-to-cube arcs only; dummy arcs are removed before applying the theorem.

That circuit extraction must establish that the order includes every selected vertex, starts immediately after the dummy, terminates immediately before it, and has exactly the stated successor arcs among its entries. This full solver-semantics-to-order argument is not implemented in the new Lean source. Local in-degree and out-degree equations alone would not replace the single-circuit premise, because they allow disconnected cycles.

The literal cube input must include both arc directions for every cube edge, no unsupported cube-to-cube arcs, and the three selection inequalities for every such edge. The Boolean interpretation of the native values and selection of every ordered vertex must be linked to the arithmetic lemma. Selection counts, restrictions to two exchanges of a saved class, any extra symmetry constraints, and enumeration coverage are outside this generic theorem.

For 193 selected cube vertices the extracted order would have 192 edges. A satisfying native assignment still needs a complete lifted vertex sequence and an independent whole-path check. A native infeasibility result retains its model and solver scope until separately certified. This preparation provides no new witness, search result, or global upper bound.
