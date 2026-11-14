# Concrete-path word capacity for all four families

PathWordCapacity215.lean imports ConcreteSupport213 and Subset211. It contains three exported results and three axiom-report commands, with two private finite-list helpers and no new definitions. No compiler or software tests were run.

The family F is explicitly selected from the literal list [chosen0, outside0, chosen1, outside1]. The actual reconstructed 99-index sequence is assumed to be an induced Q8 path with the fixed retained (0,6) coordinates and source group identifiers.

ConcreteSupport213 then gives distinct assigned raw values within F. For a duplicate-free identifier list J contained in F, equality of two assigned values forces their identifiers to agree. Thus J's assigned-value list is also duplicate-free; this is derived rather than assumed.

For any pool U containing every current domain word of every variable in J, a fitting complete assignment puts all J values in U. Subset211 therefore gives:

- A contradiction when U.length < J.length.
- Preservation of the same complete assignment when U.length = J.length and all U words are removed from the domain of a variable belonging to F but not J.

The conflict premise for that final variable is derived from the actual-path distinctness of F. The result does not permit removing U from a different chosen/outside family without a further conflict argument.

No initial-value normalization, raw-value range bound, fixed pool size, or parity-alphabet premise is needed. This argument uses only distinct assigned values and the explicit current-domain containment in U. Raw equality always implies equality of the decoded six-bit word, so the concrete path's decoded-word inequalities suffice for the raw distinctness implication.

The theorems count list lengths. A duplicate-free U is appropriate when its length should represent a domain-union set cardinality; an enclosing list is sufficient for the stated implications. U need not equal the exact union. J must be duplicate-free as an identifier list, as assumed explicitly.

The fitting assignment, domain containment, literal family selection and subset membership are retained premises. Native mask contents, candidate-subset discovery, propagation order, and complete traversal are not certified. No admitted proofs, axioms, native_decide, novelty claim, or global bound are introduced. Compilation remains pending with the parent task.
