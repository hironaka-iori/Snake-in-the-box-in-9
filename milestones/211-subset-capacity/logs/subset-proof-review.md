# Subset-capacity proof preparation

Read the complete accepted milestone 209 source, lean/Capacity209.lean. The new lean/Subset211.lean imports that unchanged module and uses its saturated_covers and domain_capacity results. No new definitions are introduced.

The four proposed deductions are:

1. Distinct assigned words, fitting the listed groups' domains, cover the pool when all those domains lie in the pool and the number of groups equals the pool length.
2. A variable whose assigned value differs from every group value cannot use a pool word under those saturation hypotheses.
3. Filtering every pool word from that variable's domain preserves the same assignment at every variable. Other constraints expressed in terms of the unchanged assignment remain unaffected.
4. A pool shorter than the list of pairwise distinct assigned values contradicts the domain-fitting and containment hypotheses.

The pool need not be an exact union for these implications: an enclosing finite list suffices. A duplicate-free pool is needed when interpreting its length as the cardinality of the available word set. Distinctness is required of assigned words, rather than merely of variable identifiers. The outside variable must conflict with every member of the chosen subset; conflicts with only some members do not justify this removal.

The preservation theorem is about each assignment satisfying the explicit hypotheses. To justify a native pruning step for every completion, the geometric model must establish these hypotheses for every such completion, and the implementation must construct the intended subset, pool, conflicts, and filtered domain. Those connections, native mask operations, traversal completeness, and a global snake bound are outside this source.

The source includes four axiom-report commands and contains no admitted proofs, new axioms, or native_decide. It was prepared without invoking Lean, a solver, or tests. Compilation and dependency pinning remain with the parent task.
