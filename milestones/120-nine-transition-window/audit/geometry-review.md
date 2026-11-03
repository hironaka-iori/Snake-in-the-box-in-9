# Source review of the outer-four geometric transfer

`lean/ActualOuter120.lean` is prepared for the parent checker. It has not been compiled in this task. The source introduces no definitions, axioms, placeholders or local-contradiction premise. Its proof structure follows the checked milestone111 `MiddleCount111.lean` interface.

The four theorem APIs are in `Snake9.ActualOuter120`:

- `outer_refuted`: the recovered local refutation for canonical word $012031$ and bounds $[(0,3),(0,3),(0,21),(0,3),(0,3)]$.
- `actual_outer_counts`: for a snake and a fitting canonical $012031$ window beginning at $r$, at least one of its four outer counts is at least4.
- `actual_forward`: exclusion of the corresponding forward `intervalHit` in a fitting nine-direction/six-count graph window, with placement $s\le1$.
- `actual_reverse`: the matching exclusion when the six-transition slice is reversed before canonicalization.

The intended actual-snake conclusion is

$$4\le\alpha_{r+1}\ \lor\ 4\le\alpha_{r+2}\ \lor\
4\le\alpha_{r+4}\ \lor\ 4\le\alpha_{r+5}.$$

The proof assumes the negation, obtains the four upper bounds3, and applies `canonical_interval_exclusion`. The middle count uses only the existing bound $\alpha_{r+3}\le21$, justified because the whole six-transition window fits. It has no additional middle restriction or sum hypothesis.

The local refutation is assembled directly from `Outer3333.sat` and `Outer3333.unsat` using `Tags.refuted_of_sat`. The generated CNF source explicitly declares `window = winOf [0,1,2,0,3,1]` and the requested five intervals. The generated semantic theorem accepts precisely `Axioms` for those centres, and the contradiction root has the expected namespace. These statements match the new wrapper. The imports are `Recovered120G.LocalWindowSat.Outer3333`, `Recovered120G.LocalWindowUnsat.Outer3333` and `ReferenceInterface`.

Both encoded bridges reuse the existing forward/reverse interval-exclusion lemmas. Their count positions are the four symbols $s,s+1,s+3,s+4$, while symbol $s+2$ is unrestricted. In actual vertex indices, those four centres are $r+s+3,r+s+4,r+s+6,r+s+7$. The interval list is symmetric under reversal; the source nevertheless uses the separate reverse geometry theorem and reverse `intervalHit`, retaining the exact direction orientation.

For the original edge18806 context, placement $s=1$ has canonical word $012031$ and symbols $(3,3,6,3,3)$. Thus this prospective rule addresses that full interval bucket without assuming the middle symbol equals6. This is an interpretation of the source statements; it is not a compilation result or a checked graph-integration claim.

There are seven requested axiom prints: the four wrapper theorems and `Outer3333.check`, `Outer3333.sat`, `Outer3333.unsat`. None has been executed here. The only remaining validation in this bounded task is the parent's successful compilation with the generated proof dependencies. No new compiler, solver or other job was started.

Pins at source review:

- `lean/ActualOuter120.lean`: `9eb3821bb7638e5194c632dd406d92913e9a0b6669c40bda9ba63ef51b0d4f94`.
- Milestone111 template `MiddleCount111.lean`: `e2a441db91bff8fa5c3c850ff389df1c34648c3e331a5f54d45fdbe72305044d`.
- Milestone85 `ReferenceInterface.lean`: `8fd1fbdf232457a880186d921a56e77a7b914c28f950400e9a512a86f5399599`.
- `data/outer3333-plan.json`: `4a71817474636cd07f45467d664578c2e37272a64440ffa09c666d163365211e`, status `GENERATED_NOT_CHECKED`,946 variables,2552 selected input clauses,5956 deductions and344241 hints. Its later completed compilation must be recorded separately.

Only `lean/ActualOuter120.lean` and this review were written. Prior evidence and the generated proof sources were not changed.
