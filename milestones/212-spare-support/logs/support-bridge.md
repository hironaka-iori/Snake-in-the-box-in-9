# Generic support bridge

SupportBridge212.lean imports the existing Spare211 and SpareSupport212 modules. It adds three proposed results and three axiom-report commands. No compiler or software tests were run.

The first result connects exception indices with unshared words. C and O are lists of variable identifiers. Their assigned-word lists must each be duplicate-free and contained in the same alphabet list. Filtering O by absence of its assigned value from the words of C, and then mapping to words, gives exactly the filtered outside-word list in Spare211.spare_capacity. Mapping preserves list length. Thus the actual exception-index list has length at most pool.length minus C.length.

The second result supplies the previously abstract missing-support implication. Every chosen-family variable with the same actual value as an outside variable must occur in that outside variable's partner list. Each such partner's actual value fits its domain, and every partner domain is contained in the support list. Consequently a value absent from support cannot occur among the chosen-family values and makes the outside index an actual exception. Support may overestimate the partner-domain union; exact equality is unnecessary for soundness.

The final result composes these deductions with the accepted exception-capacity argument. Its explicit hypotheses are:

- Distinct actual words within C and within O, with all these words in the alphabet.
- A duplicate-free list F of outside identifiers.
- Every current domain of a member of F is disjoint from its support list.
- The fixed complete assignment fits every current domain.
- For every outside variable, its partner list contains every chosen-family variable that could share its actual word.
- Its support list contains every word in each listed partner's current domain.
- F has exactly the spare alphabet capacity, and the variable being filtered belongs to O but not F.

From these premises the theorem derives the actual exception list, its capacity bound, F's inclusion in it, and the missing-support implication. It then preserves the same complete assignment after filtering the chosen outside variable's domain to supported words. A full enumeration of all forced exceptions is unnecessary: any distinct forced list that reaches capacity suffices.

Subject to successful compilation, this closes the generic bookkeeping between assigned words, exception indices, current partner domains, and the support-filter deduction. The full geometric interpretation remains separate: the square-path model must justify distinctness, the alphabet, and partner completeness. Literal interval extraction, current native masks, forced-list extraction, actual propagation order, and traversal completeness are not certified by this module.

No new global definitions, admitted proofs, axioms, native_decide, solver output, novelty claim, or snake bound are introduced. Compilation remains with the parent task.

## Separate next-step observation

For a set J of outside variables, let N(J) contain exactly those chosen-family variables y for which some x in J lists y as an allowed partner and the current domains D_x and D_y intersect. Assume the same domain-fitting, partner-completeness and distinct-word premises, with at most s actual exceptions among all outside variables.

Every nonexception member x of J shares its actual value with a unique chosen-family variable. That variable belongs to N(J), because the shared actual value lies in both domains. Distinct outside values give different partners, so these nonexception members inject into N(J). The remaining members of J are actual exceptions and number at most s. Therefore

\[
|J|\le |N(J)|+s.
\]

For the set of outside variables with no domain-supported partner, N(J) is empty and this reduces to the existing excessive-forced-exception rejection. The general inequality can detect groups competing for too few supported partners even when no individual variable lacks support. This is a written necessary condition only; no new Lean result, implementation, or search outcome is asserted.
