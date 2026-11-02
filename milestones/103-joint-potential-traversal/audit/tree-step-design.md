# Guarded potential-tree step

Current status: the parent checked this source successfully in Lean. The receipt is `data/TreeStep103-audit.json`. The design review itself started no compiler and added no concrete finite certificate.

The module imports `PotentialTree99` and adds exactly one executable helper:

`Snake9.Joint103.step (width digit : Nat) : Potential99.Tree → Option Potential99.Tree`.

A constant leaf returns itself, independently of the requested width or digit. An internal node returns its digit-selected child only when the stored width equals the requested width and the digit is between zero and five. Every other internal-node case returns `none`. The digit is zero-based; it is not the one-based symbol passed to the acceptance diagram.

The only theorem is `step_value tree child width digit offset hd hoff hs`. Its explicit premises are $d<6$, $u<w$ and successful selection of the supplied child. Its conclusion is

$$
\mathrm{value}(T,dw+u)=\mathrm{value}(T_d,u).
$$

The proof preserves constant leaves directly. For an internal node, successful selection forces the width match; the six digit cases and the residual-index bound select the same branch as the existing evaluator. Subtracting the appropriate multiple of the width leaves the residual index.

No separate positivity assumption is needed: $u<w$ already implies $w>0$. The definition permits width zero at an internal node, but no residual index can satisfy the theorem's bound in that case. This helper does not assert any global tree-shape property. The caller must supply the expected width at each digit step and handle selection failure.

No tree, potential, encoding, weight or acceptance-diagram definition is replaced. Early constant leaves remain valid without consuming tree depth. The parent's joint traversal remains responsible for the source and target digit schedules, residual-index bounds, acceptance conditions and final context-check connection.

One axiom-print command is included and passed the parent's audit. No runtime or upper-bound improvement follows from this helper alone.
