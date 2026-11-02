# Prefix potential checker

Status: source written for a separate Lean check. This task starts no compiler and supplies no completed finite potential certificate.

## Definition and invariants

The source imports the existing balanced diagram evaluator and the interval potential interface. The only new executable definition is `Snake9.PrefixChecker100.checkPrefix test depth pref node`.

The accumulator `pref` contains zero-based base-six digits. A branch index $j\in\{0,\ldots,5\}$ advances the diagram using symbol $j+1$ and updates the accumulator to $6\,\mathrm{pref}+j$. This agrees with the existing count encoder, whose update on a symbol $a$ is $6\,\mathrm{pref}+(a-1)$. The implementation uses the original encoder in its theorem statement.

Node zero returns true immediately because it rejects every continuation. At depth zero, node one evaluates `test pref`; every other node returns true because it cannot accept the empty continuation. An accepted terminal node at positive depth still visits every completion. Returning a single test at that point would omit distinct codes and would be unsound.

## Proof interface

Four declarations have axiom-print commands:

1. `evalBalanced_zero`: node zero rejects every list of symbols.
2. `checkPrefix_sound`: for any symbol list of the specified depth, with every symbol between one and six, successful prefix checking and successful diagram evaluation imply that the leaf test holds at the existing encoded value.
3. `accepted_code_of_prefix_check`: a successful depth-six traversal from the recorded root for a given saved context proves the leaf test for every accepted code below $46656$.
4. `contextCheck_of_prefix`: using the leaf test

$$
P+\pi(\mathrm{edgeTarget}(q,d,c))
\leq w(q,d,c)+\pi(\mathrm{edgeSource}(q,d,c))
$$

produces the existing `contextCheck w P π di q = true` premise. Set `w := Weights98.weight floor` to obtain the concrete weight interface.

The list induction in the second declaration selects branch $a-1$, uses the symbol bounds to justify that branch, and preserves the encoder accumulator exactly. The third declaration uses the existing balanced-evaluator equality, the six-symbol expansion of a bounded code, and the checked digit reconstruction theorem. The fourth declaration separates accepted and rejected codes; only accepted codes require the potential inequality.

Both context declarations retain the explicit premise `savedBlockClass (75*di+q) = some cls`. They evaluate the exact `recordedClassRoot cls` and preserve the full direction, history, and count key in both endpoints and the weight. Missing contexts continue to use the existing `contextCheck_missing` theorem.

## Scope and remaining work

The traversal has an arbitrary Boolean leaf test, so a later optimized leaf expression can be justified by equality without modifying the traversal proof. No graph, state numbering, count encoding, diagram acceptance definition, weight function, or floor is redefined here.

The parent must compile the source and inspect all four axiom reports. Concrete successful prefix checks, the saved-context equalities, and assembly of the required context family remain separate obligations. This source alone establishes no numerical upper bound and supplies no measured performance claim. Any reference-catalogue or floor premises required by the downstream actual-snake result remain unchanged.
