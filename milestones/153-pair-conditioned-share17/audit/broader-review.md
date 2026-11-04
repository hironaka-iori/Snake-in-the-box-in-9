# Broader critical-context certificate

The bounded independent audit found no blocker. Removing the lower count bounds at the second and fourth internal centres preserves the retained contradiction after the recorded relabelling. Both the compact core bytes and every compact proof step are identical to the exact-context certificate. The existing packed contradiction can therefore serve the broader result; a second contradiction replay is unnecessary.

The proposed broader local conclusion is share at least 17 for canonical `012032` with

\[
\alpha_1=4,\qquad \alpha_2\leq4,\qquad
\alpha_3=4,\qquad \alpha_4\leq5,\qquad \alpha_5=3.
\]

This remains a count-conditioned statement. Its Lean interpretation and actual-snake transfer are pending.

## Counter absence and input reconstruction

All counter-activity counts were independently recomputed from the original variable meanings, retained core literals, and derived proof literals. The omitted counters are old counter 4, of kind `lo 1`, with 357 registers, and old counter 8, of kind `lo 3`, with 336 registers. Neither counter has a register in the retained core or any derived clause.

Both deterministic encodings were reconstructed without invoking a solver. The exact input has 13,856 variables and 98,836 clauses. The broader input has 13,163 variables and 97,443 clauses, removing 693 registers and 1,393 clauses. Its full clause sequence and saved meanings, counters, tags, and vertex table agree with the reconstruction. No new cycle exclusion was introduced.

Register absence motivates the weakening, but the acceptance evidence also includes the complete regenerated input, retained-clause matches, and transformed proof. The conclusion does not rely on register absence alone.

## Variable, clause, and semantic-label transport

The variable map was independently reconstructed by vertex meanings and by counter kind, register row, and threshold position. It is a bijection from the retained old variables onto all 13,163 new variables. Its omitted domain consists exactly of the 693 unused registers.

The surviving old counter indices map to the new indices as follows:

| Old index | 0 | 1 | 2 | 3 | 5 | 6 | 7 | 9 | 10 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| New index | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 |

Every surviving counter retains its input literals, threshold, and semantic kind under this map. Share-variable IDs shift by 693; their meanings are unchanged. Every share-totalizer input list and its metadata agree after relabelling.

All 11,869 retained input clauses were matched to the broader input with the exact mapped literal order and multiplicity. Their selected tags agree after counter indices are replaced by their semantic kinds. This check avoids confusing numerical counter indices with unchanged mathematical meanings.

The existing 6,396-variable compact map transports to the broader variables. Applying it to the broader retained core reproduces the exact bytes of `certificates/share153.cnf`, including its active-variable header. Its SHA-256 remains:

`af20ff2875d0f0745217f740c6e9e3d4076be69c3793583537525b0c935ff32e`

## Complete proof transformation

Every line of the original and broader trimmed proofs was compared. The 30,305 deduction IDs are unchanged; every signed literal follows the variable map; every original-input hint follows the input-clause map; and all derived-clause hints retain their IDs. The proof has 1,754,767 references and 396,942 derived literal occurrences, ending at empty clause ID 190427.

The compact input ordinals are unchanged. Every compact derived clause and ordered compact hint sequence is therefore identical to the earlier certificate. This supports reuse of its already prepared packed proof, slot map, segment boundaries, and checkpoints.

The pinned broader verification record reports a complete native RUP replay in 1.281 seconds. This audit checked that record's source and artifact hashes, then independently checked the entire structural transformation. It did not repeat propagation. The receipt field `original_ids_preserved` refers to the broader input IDs supplied to that replay; the mapping explicitly records the changed IDs relative to the exact-context input.

## Required Lean work

Broader clause semantics must interpret the same compact CNF using the broader count bounds, its nine-counter table, and updated retained tags. The old exact-bound semantic theorem alone does not establish the weaker statement. In particular, the broader interpretation must not silently reuse the old exact `bounds` constant as its premise.

After the broader semantic checks and the complete existing contradiction pass, the actual-snake adapter must carry the inequalities above. Under reversal, the chronological assumptions become

\[
\alpha_1=3,\qquad \alpha_2\leq5,\qquad
\alpha_3=4,\qquad \alpha_4\leq4,\qquad \alpha_5=4.
\]

No broader Lean semantics had been generated at this audit observation. The exact 97 semantic sources and earlier frozen reviews were verified unchanged. No completed actual-snake theorem or global bound is claimed.

Only the two assigned broader-review files were written. No Lean compiler, solver, graph optimizer, repeated propagation replay, process-control action, or Git operation was run. Exact pins and comparison results are recorded in the accompanying JSON.
