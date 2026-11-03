import Recovered124G.LocalWindowSat.Total341
import Recovered124G.LocalWindowUnsat.Total341
import TotalGeometry124

namespace Snake9.ActualTotal124
open Snake9.LocalWindow Snake9.WindowAutomaton Snake9.DirectionWindow
set_option maxHeartbeats 2000000

theorem local_refuted (S E : Nat → Bool)
    (ax : Axioms S E (winOf [0,1,2,3,0,4,1])
      (centresOf (winOf [0,1,2,3,0,4,1]) [(0,21),(0,21),(0,21),(0,21),(0,21),(0,21)]))
    (hsum : absentCorners S 1 0 1 + absentCorners S 3 1 2 +
      absentCorners S 7 2 3 + absentCorners S 15 3 0 +
      absentCorners S 14 0 4 + absentCorners S 30 4 1 ≤ 24) : False := by
  obtain ⟨tau, ht⟩ := Total341.sat S E ax
    (by simpa [Total341.selected, Nat.add_assoc] using hsum)
  rw [Total341.unsat tau] at ht
  exact Bool.false_ne_true ht

theorem actual_total_sum {m : Nat} (p : Snake m) (r : Nat)
    (hr : r+7 ≤ m)
    (hshape : canon (dsOf p r 7) = [0,1,2,3,0,4,1]) :
    25 ≤ coreAlpha p (r+1)+coreAlpha p (r+2)+coreAlpha p (r+3)+
      coreAlpha p (r+4)+coreAlpha p (r+5)+coreAlpha p (r+6) :=
  TotalGeometry124.actual_total_sum local_refuted p r hr hshape

#print axioms local_refuted
#print axioms actual_total_sum
#print axioms Snake9.LocalWindow.Total341.check
#print axioms Snake9.LocalWindow.Total341.sat
#print axioms Snake9.LocalWindow.Total341.unsat
end Snake9.ActualTotal124
