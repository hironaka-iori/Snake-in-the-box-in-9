# Exact weight specialization

Status: source written for the parent's sequential Lean check. No compiler or finite certificate job was started by this task.

## Context-dependent rule filtering

The generic theorem `historyCredit_filter_emitting` equates the original history credit to the history credit of the same ordered rule list filtered by the exact suffix-emission predicate for a fixed history and direction. Its proof uses list induction. A non-emitting rule contributes zero; an emitting rule and its cap-dependent calculation remain unchanged.

This theorem has no signature-length, geometry, count-cap, direction-range or code-range premise. It supports checking a fixed context's filtered list once, then evaluating only that list for each code. No new rule datatype or evaluator is introduced.

## Short histories

If the stored history has fewer than two direction IDs, appending one ID produces fewer than three IDs. A signature of length three therefore cannot be a suffix. The generic contribution and aggregate-credit equalities use only this length argument.

For the concrete 55-rule catalogue, the signature-length premise is extracted from the first component of the existing `concrete_rules_valid` theorem. In particular, history index zero has the empty prefix, so its history credit is zero for every direction and code. No graph-range premise is required.

The resulting weight identity is

$$
w_F(q,d,c)
=120(c\bmod6+1)
+\max\!\left(g_d,\max\!\left(b(d,c),F(d)\right)\right)
$$

whenever the prefix at $q$ has length less than two. Here $g_d$ is the original geometric lookup and $b(d,c)$ is the original conditioned credit. All alternatives retain their maximum operation.

## Benchmark contexts

For direction35 and history0, the source includes closed lookup and canonical-shape subproofs. The geometric credit is zero. The forward six-direction suffix has canonical shape $012034$, while the reversed shape is $012342$. Only the existing conditioned rule with symbols $(6,3,6,3,3)$ can contribute. Its encoded value is7106 and its credit is96. The exact proposed all-code equality is

$$
w_F(0,35,c)
=120(c\bmod6+1)
+\max\!\left(
\begin{cases}
96,&c\bmod7776=7106,\\
0,&c\bmod7776\ne7106,
\end{cases}
F(35)\right).
$$

The completed floor at35 is zero and the weaker conditional floor is18. Separate declarations specialize the equality to those two existing floor functions.

For direction177 and history43, the filtered list is empty. The source checks that exact list equality, uses the generic filtering theorem, checks both canonical suffix orientations as $012301$, and obtains conditioned credit zero. The geometric credit is8 and the conditional floor is16. This gives

$$
w_{\mathrm{conditional}}(43,177,c)=120(c\bmod6+1)+16
$$

for every natural count code.

These are equalities of executable weight definitions. They require no pending local-refutation premise. Using a conditional weight as an actual-snake bound still requires the original five explicit local-refutation premises.

## Evidence and limits

The source directly reuses the existing evaluator, concrete rules, geometry table, conditioned credits, count-free credits and combined weight through `CombinedWeights98`. It does not change any saved rule, count interpretation, share scale, state numbering or endpoint formula.

Thirteen axiom-print commands cover filtering, short-history results and the two concrete context specializations. Compilation, printed axioms, potential inequalities and measured performance remain separate checks. The source includes no placeholder proofs. No numerical upper-bound improvement is asserted here.
