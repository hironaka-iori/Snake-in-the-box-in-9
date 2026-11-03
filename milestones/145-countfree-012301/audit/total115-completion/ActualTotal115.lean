import Refined115.LocalWindowSat.Total310
import Refined115.LocalWindowUnsat.Total310
import TotalGeometry114

namespace Snake9.ActualTotal115
open Snake9.LocalWindow Snake9.WindowAutomaton Snake9.DirectionWindow
set_option maxHeartbeats 2000000

theorem local_refuted (S E : Nat → Bool)
    (ax : Axioms S E (winOf [0,1,2,3,1,0])
      (centresOf (winOf [0,1,2,3,1,0]) [(0,21),(0,21),(0,21),(0,21),(0,21)]))
    (hsum : absentCorners S 1 0 1 + absentCorners S 3 1 2 +
      absentCorners S 7 2 3 + absentCorners S 15 3 1 +
      absentCorners S 13 1 0 ≤ 18) : False := by
  obtain ⟨tau, ht⟩ := Total310.sat S E ax
    (by simpa [Total310.selected, Nat.add_assoc] using hsum)
  rw [Total310.unsat tau] at ht
  exact Bool.false_ne_true ht

theorem actual_total_sum {m : Nat} (p : Snake m) (r : Nat)
    (hr : r+6 ≤ m)
    (hshape : canon (dsOf p r 6) = [0,1,2,3,1,0]) :
    19 ≤ coreAlpha p (r+1)+coreAlpha p (r+2)+coreAlpha p (r+3)+
      coreAlpha p (r+4)+coreAlpha p (r+5) :=
  TotalGeometry114.actual_total_sum local_refuted p r hr hshape

#print axioms local_refuted
#print axioms actual_total_sum
#print axioms Snake9.LocalWindow.Total310.check
#print axioms Snake9.LocalWindow.Total310.sat
#print axioms Snake9.LocalWindow.Total310.unsat
end Snake9.ActualTotal115
