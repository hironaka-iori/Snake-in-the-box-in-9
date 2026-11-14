# Support filtering from the concrete indexed path

PathSupport213.lean imports ConcreteSupport213 and SupportBridge212. It contains two exported theorems and two axiom-report commands, with no new definitions. No compiler or software tests were run.

Both theorems assume that the reconstructed 99-index vertex sequence is an induced Q8 path, using the literal retained (0,6) coordinates, source-derived group identifiers, and six-bit decoding of a raw natural-number assignment.

The accepted concrete family results then supply:

- Distinct assigned words in the chosen family.
- Distinct assigned words in the outside family.
- Membership in the literal partner list for every actual chosen/outside sharing pair.

The composition retains these further premises explicitly:

- A pool list of length 32 contains every current domain word for the relevant chosen and outside variables.
- The same complete assignment fits all current domains.
- F is a duplicate-free list of outside variables, each having a domain disjoint from its support list.
- Each outside support list contains every current domain word of its listed partners.
- The variable being filtered is outside the chosen family and is absent from F.

Small kernel-decided length goals give 30 chosen even variables and 26 chosen odd variables. Thus F.length = 2 in the even theorem and F.length = 6 in the odd theorem are exactly the saturation requirements of SupportBridge212.saturated_support_preserves_assignment. Its derived exception budget and support argument preserve the same assignment at every variable after intersecting the selected outside domain with its support list.

An explicit 32-entry pool is used instead of adding a new parity-alphabet definition. This is sufficient for the finite capacity implication. Applying the result to concrete parity masks still requires establishing their length and domain-containment premises; these are not inferred solely from the decoded path.

Subject to successful compilation, this composes the actual source-specific path geometry with both support-filter rules. It does not prove that every native assignment constructs a path, identify the contents of native masks, or certify the implementation or complete traversal. Compilation remains with the parent task.
