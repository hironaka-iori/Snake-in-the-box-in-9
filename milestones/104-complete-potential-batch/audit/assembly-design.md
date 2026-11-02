# Assembly from saved block certificates

Status: generic source written for the parent's Lean check. This task starts no compiler and supplies no completed finite context batch.

The module imports `PotentialChecker99` and adds one theorem, `Snake9.GraphAssembly104.graphCheck_of_saved_blocks`. No definitions are introduced.

Its explicit premise supplies the original `contextCheck` certificate for every entry in `Snake9.Batch92.savedBlockClasses`, decoding an entry's key by quotient and remainder modulo75. The conclusion is the original `graphCheck w P π = true`, with no change to its direction, history or count ranges.

The proof introduces an arbitrary direction and history from the two checked ranges, then splits the underlying saved-block search. A failed search gives `savedBlockClass (75*di+q) = none` by its definition. The existing `contextCheck_missing` theorem handles that whole context without evaluating its count codes.

A successful search supplies both list membership and the exact key equality through the standard `List.mem_of_find?_eq_some` and `List.find?_some` lemmas. The bound $q<75$ then gives

$$
\left\lfloor\frac{75d+q}{75}\right\rfloor=d,
\qquad
(75d+q)\bmod75=q.
$$

The corresponding saved-entry certificate is therefore already the required context certificate. This directly assembles the two Boolean universal checks, avoiding a redundant second proof for each code.

The argument does not require saved-list uniqueness, any separate class-index bound, or evaluating the list's791 concrete entries. It neither evaluates all37875 possible contexts nor expands `generatedRows`. The explicit saved-entry premise remains to be discharged by the complete batch; there is no claim here that the batch has finished.

The existing `graphCheck_sound` theorem can subsequently convert the result to the row potential inequality. Original reference-catalogue and conditional-floor premises remain at their existing actual-snake interfaces.

One axiom-print command is included. The imported list-search lemmas were checked against the local Lean4.19 source, but this module has not been compiled in this task. Remaining verification is ordinary elaboration and inspection of the printed axioms; no unresolved mathematical premise beyond the stated saved-entry certificates was identified.
