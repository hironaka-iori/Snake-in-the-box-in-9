# Independent source review of the second reference recovery

This review covers the copied sources and data for `D012304A22623`, plus the proposed list reduction. No Lean compiler, solver, or certificate replay was run. The proof text below is uncompiled and must be checked by the parent before use.

## Exact semantic target

Milestone107 `data/older-alternatives.json` identifies this root with original reference-union index 472. The exact key is

```lean
([0, 1, 2, 3, 0, 4], [2, 2, 6, 2, 3])
```

The copied Cnf source defines its window as `winOf [0,1,2,3,0,4]` and its bounds as `boundsOf [2,2,6,2,3]`. In the existing model these evaluate respectively to

```text
window = [0,1,3,7,15,14,30]
bounds = [(2,2),(2,2),(6,21),(2,2),(3,3)]
```

In particular, symbol 6 allows every count from 6 through 21. It does not impose equality to 6. The intended theorem is exactly

```lean
Refuted (winOf [0, 1, 2, 3, 0, 4]) (boundsOf [2, 2, 6, 2, 3])
```

The Sat source's `sat` theorem takes the corresponding `Axioms S E window (centresOf window bounds)` premise and supplies a satisfying assignment for that same case CNF. Once its contradiction theorem is checked, `Tags.refuted_of_sat D012304A22623.sat D012304A22623.unsat` supplies the intended local refutation. This depends on the actual checked case modules, including their semantic `check` theorem; source inspection alone does not establish the result.

The copied metadata matches both lists, the reconstructed window, and all five bounds. Independently decoding all 120 natural-number Lean raw clauses gave exact equality with the clauses selected by `core_ids` from the copied 29,055-clause CNF. This verifies the intended input correspondence, not the validity of the regenerated LRAT proof.

## Removing the two proved keys

The existing checked milestone107 theorem reduces the full union obligation to `AllRefutedList referenceKeys.tail`. Original index 472 becomes index 471 after taking the tail. Therefore the direct remaining list is

```lean
referenceKeys.tail.eraseIdx 471
```

It preserves the order of all other entries and removes original indices 0 and 472. Its length computed from the exact saved union is 1,376. No assumption of unique keys is needed for this indexed deletion argument.

The following small generic theorem uses only the recursive `AllRefutedList` definition and standard list equations. Its out-of-range case is also valid: the premise is vacuous and erasing an absent index leaves the list unchanged.

```lean
open Snake9.LocalWindow Snake9.Reference85

theorem allRefutedList_eraseIdx_iff
    (l : List (List Nat × List Nat)) (i : Nat)
    (h : ∀ k, l[i]? = some k →
      Refuted (winOf k.1) (boundsOf k.2)) :
    AllRefutedList l ↔ AllRefutedList (l.eraseIdx i) := by
  induction l generalizing i with
  | nil => simp [AllRefutedList]
  | cons a l ih =>
      cases i with
      | zero =>
          have ha : Refuted (winOf a.1) (boundsOf a.2) := h a rfl
          change (Refuted (winOf a.1) (boundsOf a.2) ∧
            AllRefutedList l) ↔ AllRefutedList l
          exact ⟨And.right, fun hl => ⟨ha, hl⟩⟩
      | succ i =>
          change (Refuted (winOf a.1) (boundsOf a.2) ∧
            AllRefutedList l) ↔
            (Refuted (winOf a.1) (boundsOf a.2) ∧
              AllRefutedList (l.eraseIdx i))
          exact and_congr Iff.rfl
            (ih i (fun k hk => h k (by simpa using hk)))

theorem reference_union_iff_remaining_two
    (hcase : Refuted (winOf [0, 1, 2, 3, 0, 4])
      (boundsOf [2, 2, 6, 2, 3])) :
    AllRefutedList referenceKeys ↔
      AllRefutedList (referenceKeys.tail.eraseIdx 471) := by
  have h472 : (referenceKeys.tail)[471]? =
      some ([0, 1, 2, 3, 0, 4], [2, 2, 6, 2, 3]) := by
    decide +kernel
  have hremove : AllRefutedList referenceKeys.tail ↔
      AllRefutedList (referenceKeys.tail.eraseIdx 471) :=
    allRefutedList_eraseIdx_iff _ _ (by
      intro k hk
      have heq : k = ([0, 1, 2, 3, 0, 4], [2, 2, 6, 2, 3]) :=
        Option.some.inj (hk.symm.trans h472)
      subst k
      exact hcase)
  exact Snake9.RecoveredReference107.reference_union_iff_remaining.trans hremove

theorem remaining_two_key_count :
    (referenceKeys.tail.eraseIdx 471).length = 1376 := by
  decide +kernel
```

This introduces no new mathematical definition. The new generic lemma is optional if the parent prefers an equivalent direct list induction. The lookup equation and length equation are finite statements still requiring kernel checks. All other reference entries remain obligations; the source comparison of older alternatives does not discharge them.

## Reviewed byte hashes

Copied case inputs are under `milestones/107-reference-refutation-recovery/upstream`. Hashes are SHA-256.

| Artifact | Hash |
|---|---|
| `data/older-alternatives.json`, outside `upstream` | `553f52717a9a30741fc1a655bd4c9046450a0ffae44f1c2f3d06471c96f14d00` |
| `work/final_lean/LocalWindowCnf/D012304A22623.lean` | `21a9fc070053b485acbd5fa92b12b6d0809cf34ee49ab8d4e96b8341aed04372` |
| `work/final_lean/LocalWindowSat/D012304A22623.lean` | `99708d59913a518f14da6186710ffcf02ba18df9be655357bb20974ee4a0b2ee` |
| `milestones/10-window-aggregate/data/lean_core_direction5/d012304_a2_2_6-21_2_3.json` | `a624e1df1a2956dd08c049c4f340e8b395c4c6b6e2015d8826eda05c4d971e8d` |
| `milestones/10-window-aggregate/certificates/direction/d012304_a2_2_6-21_2_3.cnf.gz` | `41bc1f5303637df2d80cbe28d1da58dfaaa63f568e64001fbdc4c77e7ed5e7f2` |

Only this review note was written. The parent owns generation, replay, and all final kernel-check claims.
