# Review of a relaxed count condition for D012304A22623

The proposed relaxation is supported by the checked source dependencies and an independent arithmetic inspection. Its new semantic certificate has not been checked in Lean by this reviewer. No compiler, solver, or proof replay was launched, and no existing source or report was modified.

## Proposed statement

For the same canonical window, use the explicit bounds list

```lean
[(0, 2), (0, 21), (0, 21), (0, 2), (0, 3)]
```

The target is

```lean
Refuted (winOf [0, 1, 2, 3, 0, 4])
  [(0, 2), (0, 21), (0, 21), (0, 2), (0, 3)]
```

This would exclude the simultaneous inequalities $a_1\le2$, $a_4\le2$, and $a_5\le3$ for the five centres of this window, with the second and third counts arbitrary in their natural range $0\le a_i\le21$. It still uses the existing local `Axioms` interface. A general actual-snake statement requires the existing canonical-window transport and the facts placing the other counts in that range. This is a proposed strengthened exclusion, with no novelty claim.

Use literal interval pairs. `boundsOf` of a symbol list cannot express these intervals: symbols below 6 give exact values, while symbol 6 gives `[6,21]`.

## What the checker actually validates

In `work/final_lean/LocalWindowTags.lean`, `checkAll` is

```lean
cs.all (ctrOK M (centresK w b)) && ckAll M cs w tags raw
```

Thus it checks **all counters in the metadata list**, including counters not referenced by any retained clause. Changing only the bounds causes six counter-validity conditions to fail.

For a `.hi ci` counter, `ctrOK` requires its negative primary literals to enumerate exactly the centre's free corners and its `k` to equal that centre's upper bound. For a `.lo ci` counter, it requires the corresponding positive primary literals and `k + lo` equal to the number of free pairs. Here every centre has 21 free pairs. The endpoint counter has its separate fixed limit 2.

The original clause tags are exactly 6 window tags, 22 degree-at-most-two tags, 2 positive-degree tags, and 90 counter tags. Counter indices 1, 6, and 8 occur respectively 49, 12, and 29 times. Their meanings are upper bounds on zero-based centres 0, 3, and 4. Independently parsing the `meaning` tree and resolving every variable appearing in the raw clauses found 51 primary variables and 55 register variables. All register variables belong to counters 1, 6, or 8; there are no endpoint-variable occurrences in the raw clauses.

## Exact metadata edits

Keep the list length, order, literal lists, counter kinds, meaning tree, tags, window, and raw CNF unchanged. Modify only the six indicated counter limits:

| Counter index | Kind | Original `k` | Relaxed `k` |
|---:|---|---:|---:|
| 0 | `.ends` | 2 | 2 |
| 1 | `.hi 0` | 2 | 2 |
| 2 | `.lo 0` | 19 | **21** |
| 3 | `.hi 1` | 2 | **21** |
| 4 | `.lo 1` | 19 | **21** |
| 5 | `.lo 2` | 15 | **21** |
| 6 | `.hi 3` | 2 | 2 |
| 7 | `.lo 3` | 19 | **21** |
| 8 | `.hi 4` | 3 | 3 |
| 9 | `.lo 4` | 18 | **21** |

All five lower-bound counters now express the trivial lower bound zero through `k + 0 = 21`. The unused upper-bound counter at index 3 now expresses the trivial upper bound 21. There is no upper-bound counter for centre 2 in the original list, and adding one is unnecessary.

An independent Python inspection using the parsed literal meanings and the exact free-pair order found all ten original `ctrOK` conditions true. Under the new bounds with unchanged metadata, indices 2, 3, 4, 5, 7, and 9 fail. After precisely the edits above, all ten conditions are true. This computation checks the intended arithmetic and data correspondence; it is not a Lean theorem.

## Why the existing CNF can be reused

`ckAll` does not receive the bounds list. The only change to its counter data is `k` in six counters which no clause tag references. In particular, the `.over` clauses still see their original limits 2, 2, and 3. The counter literals used by `.first` and `.step` are unchanged. The `.mono` and `.zero` checks use the meaning tree, which is also unchanged. The non-counter clauses are unchanged. These source dependencies support preservation of the clause-check result.

Moreover, `tau` interprets a register using the counter's `lits` and the register indices. It does not inspect the counter's `k` or `kind`. Changing only these six `k` values therefore leaves the induced assignment unchanged. Preserving counter positions is essential because both the meaning tree and clause tags refer to their numerical indices.

The implementation should create a separate relaxed semantic theorem or module. It need not alter the archived Cnf/Sat sources or regenerate a contradiction proof. First prove in Lean

```lean
checkAll D012304A22623.meaning relaxedCtrs
  D012304A22623.window
  [(0, 2), (0, 21), (0, 21), (0, 2), (0, 3)]
  D012304A22623.tags D012304A22623.raw = true
```

using the existing kernel evaluation method. Then apply `Tags.sound` with those relaxed bounds and counters to produce satisfiability of the unchanged raw CNF from the relaxed axioms. Finally combine that semantic theorem with the checked `D012304A22623.unsat` through `Tags.refuted_of_sat`. The CNF equality is definitional because its raw clauses and decoding are unchanged. The remaining obligations are this new semantic check, successful theorem elaboration, and the usual axiom audit. Extending graph filters or counting newly covered catalogue keys is outside this review.

## Sources and scope

The case sources are the copied milestone107 inputs already pinned in `independent-review.md`: Cnf SHA-256 `21a9fc070053b485acbd5fa92b12b6d0809cf34ee49ab8d4e96b8341aed04372`, Sat SHA-256 `99708d59913a518f14da6186710ffcf02ba18df9be655357bb20974ee4a0b2ee`. The inspected `LocalWindowTags.lean` hash is `1e9aad3e4c99acf4fa01b00dcc65330a8d633826079a3d0955716ccb0f36ec71`.

Relevant source locations are `ctrOK` at line 201, the clause checks at lines 242–280, `checkAll` at line 286, `tau` at line 107, and `sound` at line 749. The model's free-pair enumeration and explicit lower/upper-bound axioms are in `LocalWindowModel.lean` at lines 30–69. These were inspected directly. This report does not assert that the relaxed theorem has passed the kernel.

Subsequent parent-reported status: `RelaxedReference108.lean` passed Lean with the six proposed counter-limit changes held in a local `let`, checking all counter metadata and reusing the same contradiction theorem. The parent reports only `propext`, `Classical.choice`, and `Quot.sound` in its axiom audit. This is separate from this reviewer's read-only inspection; this reviewer did not run that check or independently audit its receipt. Generic transfer to narrower bounds and deletion of additional union entries remain separate integration work.
