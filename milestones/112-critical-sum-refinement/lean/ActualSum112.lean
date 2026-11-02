import Refined112.LocalWindowSat.Sum3142
import Refined112.LocalWindowUnsat.Sum3142
import SumGeometry112

namespace Snake9.ActualSum112
open Snake9.LocalWindow Snake9.WindowAutomaton Snake9.DirectionWindow
set_option maxHeartbeats 2000000

theorem local_refuted (S E : Nat → Bool)
    (ax : Axioms S E (winOf [0,1,2,3,1,4])
      (centresOf (winOf [0,1,2,3,1,4]) [(0,21),(0,21),(0,2),(0,21),(0,21)]))
    (hsum : absentCorners S 1 0 1 + absentCorners S 3 1 2 +
      absentCorners S 15 3 1 + absentCorners S 13 1 4 ≤ 18) : False := by
  obtain ⟨tau, ht⟩ := Sum3142.sat S E ax
    (by simpa [Sum3142.selected, Nat.add_assoc] using hsum)
  rw [Sum3142.unsat tau] at ht
  exact Bool.false_ne_true ht

theorem actual_outer_sum {m : Nat} (p : Snake m) (r : Nat)
    (hr : r+6 ≤ m)
    (hshape : canon (dsOf p r 6) = [0,1,2,3,1,4])
    (hmiddle : coreAlpha p (r+3) ≤ 2) :
    19 ≤ coreAlpha p (r+1)+coreAlpha p (r+2)+
      coreAlpha p (r+4)+coreAlpha p (r+5) :=
  SumGeometry112.actual_outer_sum local_refuted p r hr hshape hmiddle

theorem comparison_cannot_exclude_235 (p d R : Nat) (hp : p ≤ 484*d) :
    (4200*d+p)*235 ≤ 1098960*d+8*p+R := by omega

theorem conditional_comparison_cannot_exclude_234 (p d R : Nat)
    (hp : p ≤ 496*d) :
    (4200*d+p)*234 ≤ 1098960*d+8*p+R := by omega

#print axioms local_refuted
#print axioms actual_outer_sum
#print axioms comparison_cannot_exclude_235
#print axioms conditional_comparison_cannot_exclude_234
#print axioms Snake9.LocalWindow.Sum3142.check
#print axioms Snake9.LocalWindow.Sum3142.sat
#print axioms Snake9.LocalWindow.Sum3142.unsat
end Snake9.ActualSum112
