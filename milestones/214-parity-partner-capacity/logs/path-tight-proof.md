# Tight filtering from the normalized concrete path

PathTight214.lean imports ConcreteSupport213, PathParity214 and TightPartner214. It contains two exported theorems with two axiom-report commands. No compiler or software tests were run.

The path premise is the source-specific 99-index reconstruction for retained coordinates (0,6), with six-bit decoding of raw assigned values. The assignment starts with values(0)=0 and has values(g)<64 for every g<78.

Small kernel goals check that every identifier in the even chosen/outside lists is below 78 and even, and every identifier in the odd lists is below 78 and odd. PathParity214.normalized_pool_membership then places their actual values in the corresponding parity pools. The two word-decoding definitions are definitionally equal. The accepted pool_lengths theorem supplies 32 words in each pool.

ConcreteSupport213 supplies chosen-word distinctness, outside-word distinctness and the literal partner-completeness implications. The chosen-family lengths are 30 and 26, checked by small kernel goals. Therefore the tight equalities become |J|=|N|+2 for even parity and |J|=|N|+6 for odd parity.

The composition retains these premises:

- J's assigned words are distinct, and every member of J belongs to the relevant outside list.
- The same complete assignment fits every current domain.
- N contains every listed chosen partner of a J member whose two current domains intersect.
- The variable being filtered is outside the chosen family and absent from J.
- Its support list contains every domain word of its listed chosen partners outside N.

TightPartner214 then proves that the filtered variable's actual value remains in support. Filtering its domain to that support preserves the same assignment at every variable.

Compared with the earlier explicit-pool composition, actual alphabet membership and pool size are now derived from normalization, bounded values and the checked path-parity results. This does not assert that every possible word in every current domain belongs to the corresponding pool; only actual assigned values are needed for the capacity argument.

Subject to successful compilation, the file composes the normalized actual-path premise through parity capacity to both tight-subset filters. Literal current-domain masks, candidate extraction, propagation, normalization coverage for arbitrary inputs, and complete native traversal are outside its claims. No new generic definitions, admitted proofs, axioms, native_decide, novelty, or global bound are introduced. Compilation remains pending with the parent task.
