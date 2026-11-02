import Recovered108.LocalWindowSat.D012304A22623
import Recovered108.LocalWindowUnsat.D012304A22623
import RecoveredReference107

namespace Snake9.RecoveredReference108
open Snake9.LocalWindow Snake9.Reference85
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem second_reference_refuted :
    Refuted (winOf [0, 1, 2, 3, 0, 4]) (boundsOf [2, 2, 6, 2, 3]) :=
  Tags.refuted_of_sat D012304A22623.sat D012304A22623.unsat

theorem second_reference_key :
    referenceKeys[472]? = some ([0, 1, 2, 3, 0, 4], [2, 2, 6, 2, 3]) := by
  decide +kernel


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

theorem reference_union_iff_remaining_two :
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
      exact second_reference_refuted)
  exact Snake9.RecoveredReference107.reference_union_iff_remaining.trans hremove

theorem remaining_two_key_count :
    (referenceKeys.tail.eraseIdx 471).length = 1376 := by
  decide +kernel

#print axioms second_reference_refuted
#print axioms second_reference_key
#print axioms allRefutedList_eraseIdx_iff
#print axioms reference_union_iff_remaining_two
#print axioms remaining_two_key_count
#print axioms Snake9.LocalWindow.D012304A22623.check
#print axioms Snake9.LocalWindow.D012304A22623.sat
#print axioms Snake9.LocalWindow.D012304A22623.unsat
#print axioms Snake9.LocalWindow.D012304A22623.ok1
end Snake9.RecoveredReference108
