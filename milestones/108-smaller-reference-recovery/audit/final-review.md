# Final independent review of milestone108

No blocking mathematical or coverage issue was found in the reviewed sources and saved evidence. This was a read-only review of `RecoveredReference108.lean`, `RelaxedReference108.lean`, `ReferenceCoverage108.lean`, the proof summary, and the three wrapper receipts and logs. No compiler, solver, or proof replay was launched. Only this report was written.

## Mathematical checks

The relaxed theorem has the intended explicit bounds

```lean
Refuted (winOf [0, 1, 2, 3, 0, 4])
  [(0, 2), (0, 21), (0, 21), (0, 2), (0, 3)]
```

Its local counter edits affect only indices 2, 3, 4, 5, 7, and 9. The theorem checks all counter metadata against these bounds, obtains satisfiability of the unchanged CNF from the relaxed axioms, and combines this with the recovered contradiction. It does not infer relaxation merely from the original exact-count refutation.

The direction of `refuted_of_tighter_centres` is correct. For every centre $d$ of the already-refuted relaxed bounds, it finds a centre $e$ of the proposed tighter bounds at the same vertex and with the same two directions. Its hypotheses are

$$
d.\mathrm{lo}\le e.\mathrm{lo},\qquad e.\mathrm{hi}\le d.\mathrm{hi}.
$$

Thus an assignment satisfying the tighter axioms also satisfies the relaxed bounds: $d.\mathrm{lo}\le e.\mathrm{lo}\le\alpha$ and $\alpha\le e.\mathrm{hi}\le d.\mathrm{hi}$. All other fields of `Axioms` are preserved. Requiring such a match for every relaxed centre is sufficient; the tighter list may contain additional constraints. There is no reversal of the needed implication.

`allRefutedList_filter_iff` is also correct. A key in the proved list is already refuted, so deleting it leaves an equivalent conjunction of outstanding refutations. A key outside that list remains in the filtered list. The induction proves both directions and does not assume that either list has distinct entries or that every proved key appears in the original list. The subsequent concrete length theorem independently fixes the number of remaining entries.

The seven transfers use `Tags.centresK_eq` before kernel evaluation. This rewrites to an equal executable centre computation, preserving the statement. It resolves the earlier reduction failure involving `dirOfStep`/`Nat.log2`; it does not add a mathematical premise or approximate the directions.

## Exact coverage

The eight proved keys are distinct and occur at the stated positions of the exact milestone85 union:

| Original index | Directions | Symbols |
|---:|---|---|
| 0 | `[0,1,2]` | `[1,1]` |
| 472 | `[0,1,2,3,0,4]` | `[2,2,6,2,3]` |
| 495 | `[0,1,2,3,0,4]` | `[2,3,6,2,3]` |
| 535 | `[0,1,2,3,0,4]` | `[2,4,6,2,3]` |
| 572 | `[0,1,2,3,0,4]` | `[2,5,6,2,3]` |
| 602 | `[0,1,2,3,0,4]` | `[2,6,4,2,3]` |
| 619 | `[0,1,2,3,0,4]` | `[2,6,6,2,2]` |
| 620 | `[0,1,2,3,0,4]` | `[2,6,6,2,3]` |

Symbol 6 continues to mean the complete interval `[6,21]`. Each of the seven longer-window keys is contained in the relaxed interval bounds. An independent comparison with the saved 1,378-key union confirmed the indices and that the filter removes exactly eight entries, leaving 1,370. This agrees with the checked `remaining_eight_key_count` theorem. The full-union equivalence retains every unresolved key as an explicit obligation.

## Saved proof evidence

All nine receipt hashes listed in `data/proof-summary.json` match the current receipt files. For each of the three wrappers, the current Lean source, preserved source snapshot, compiled object, and successful log match their recorded hashes. Each wrapper receipt reports exit code 0 and no timeout. The 15 theorem-audit entries in the summary agree with the three wrapper audit lists and the printed logs. Their combined axiom set is exactly `propext`, `Classical.choice`, and `Quot.sound`; several individual statements use fewer or no axioms. No `sorry`, `admit`, `native_decide`, or new `axiom` declaration occurs in the three wrapper sources.

The proof-summary SHA-256 at review is `acbfa144153fade9d1f8a7162691ccc377692ccccab4e3703758251f2ef314e2`.

| Wrapper | Source SHA-256 | Successful receipt SHA-256 |
|---|---|---|
| `RecoveredReference108` | `38bef72bcd4775bbb5336f1396337bc5dc84deb70f772e0a3a39f36958bb710d` | `f988cec841fe8daae4cd4bb92d2cce4f4a2d28d914cff783a002968b287468e5` |
| `RelaxedReference108` | `6afbbc5888e266e010566038229e80e16dfa6d1b2fe537b079b5ead3fb146820` | `420706f34c7693306bbdda9e95261f9e841a9524da8fc8c39c05fcf6407fea75` |
| `ReferenceCoverage108` | `1c9ce36588bd8cd5dfb75f06b45f8abecb3ed903d925ca1b4f062d1d83e68a75` | `a3a3e2512835801bdf0371d79e93002bc966e128a0f20b5e74b868b3d95d856d` |

The earlier failed coverage attempt is preserved as `logs/ReferenceCoverage108-1793652781987009000.log`, SHA-256 `9e9318f37cf09a9add3d24a7979778a54413def9e3b18521348b88268cf97305`, together with its source snapshot. The successful receipt points to the later `1793652827765497600` attempt. The failed attempt is not counted as checked evidence.

This review did not rebuild or rehash the entire inherited dependency closure. It verifies the stated local wrapper evidence and its agreement with the summary.

## Scope and continuation

These are closed refutations for the existing local `Axioms` interface. Their application to arbitrary actual snake windows uses the established normalization and local-axiom transport. No new direct actual-snake theorem is introduced in these wrappers. The full reference union remains equivalent to an unresolved 1,370-entry obligation. The summary correctly states `full_reference_union_checked: false` and makes no new numerical upper-bound claim.

The highest-value next investigation is to inspect the count constraints actually required by other small cores before recovering one proof per exact key. For each candidate, identify the counter limits inspected by retained clause tags, test a consistent relaxation of unnecessary bounds, check the new semantic certificate against the unchanged CNF, and then use the checked centre-weakening theorem to cover exact remaining keys.

The source suggests a more precise screening criterion than simply counting referenced counters: `.over` inspects a counter's `k`, whereas `.first`, `.mono`, `.step`, and `.zero` do not. A counter referenced only by those other clause families may permit a changed limit while preserving its literal list, register meanings, and clause checks. `checkAll` still validates every counter, so all changed metadata must agree with the proposed bounds. This extension has not been tested on other cores. Rank candidates by newly covered unresolved keys and recorded proof size, and require a new kernel check before accepting any broader exclusion. The present seven-key result establishes the value of testing this route; it does not predict how much of the remaining union it will cover.
