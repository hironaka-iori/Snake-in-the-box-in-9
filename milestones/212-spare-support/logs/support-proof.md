# Exception capacity and partner support

SpareSupport212.lean imports the unchanged Capacity209 module and contains four proposed deductions, each with an axiom-report command. It was prepared without compiling or running tests.

For one complete assignment, E is a finite list of actual exception-variable identifiers, F is a duplicate-free list of forced exception identifiers, and every member of F belongs to E. The capacity premise is E.length <= s.

1. Capacity209.distinct_length_le gives F.length <= E.length. Hence F.length > s is impossible.
2. If F.length = s, the same inequality and the capacity premise force F.length = E.length. Capacity209.saturated_covers then gives E contained in F.
3. For a chosen variable outside F, suppose its actual value being absent from the support list would place that variable in E. Saturation then contradicts its absence from F, so the value must belong to the support list.
4. Intersecting the chosen variable's domain with that support list preserves the same complete assignment at every variable. Every other constraint expressed on this unchanged assignment remains satisfied.

No duplicate-free assumption on E is required for these implications. A list containing each actual exception exactly once is the natural interpretation when its length is to count exception variables. Duplicate entries in E would only strengthen the stated numerical premise.

For the intended application, an exception is an outside interval whose actual word is absent from the chosen clique's words. The geometric spare-capacity argument must provide the bound on E. To place an interval in F, the model must establish that its actual word cannot have an antipodal partner in every completion under consideration. An empty intersection between its current domain and the union of its possible partners' current domains is sufficient once domain-fitting and partner completeness are established.

The support list for another outside interval is that union of possible antipodal partner domains. If its actual value lacks this support, it cannot equal an actual partner value, so the required unsupported-value-to-exception implication follows from the geometric partner rule and the partners' domain membership. Membership in the support list alone does not guarantee a compatible partner assignment.

The native application must establish these premises for every preserved completion, including after domains change. A guessed forced list, an incomplete partner list, or support measured against stale domains is not certified by the abstract statement. The full geometry-to-model connection, concrete exception enumeration, mask operations and traversal remain separate obligations.

No new definitions, admitted proofs, axioms, native_decide, novelty claim, or global-bound claim are introduced. Compilation remains pending with the parent task.
