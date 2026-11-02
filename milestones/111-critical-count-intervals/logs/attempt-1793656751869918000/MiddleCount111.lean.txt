import Refined111.LocalWindowSat.Middle325R
import Refined111.LocalWindowUnsat.Middle325R
import ReferenceInterface

namespace Snake9.MiddleCount111
open Snake9.LocalWindow Snake9.WindowAutomaton Snake9.DirectionWindow
open Snake9.GraphInterpretation75 Snake9.GraphWalk78 Snake9.CountGeometry78
open Snake9.Guards79
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem middle_refuted :
    Refuted (winOf [0,1,2,3,4,0])
      [(0,21),(0,3),(0,2),(0,5),(0,21)] :=
  Tags.refuted_of_sat Middle325R.sat Middle325R.unsat

theorem actual_three_counts {m : Nat} (p : Snake m) (r : Nat)
    (hr : r+6 ≤ m)
    (hshape : canon (dsOf p r 6) = [0,1,2,3,4,0]) :
    4 ≤ coreAlpha p (r+2) ∨ 3 ≤ coreAlpha p (r+3) ∨
      6 ≤ coreAlpha p (r+4) := by
  by_contra hn
  have h₂ : coreAlpha p (r+2) ≤ 3 := by omega
  have h₃ : coreAlpha p (r+3) ≤ 2 := by omega
  have h₄ : coreAlpha p (r+4) ≤ 5 := by omega
  apply canonical_interval_exclusion p r 6 [0,1,2,3,4,0]
    [(0,21),(0,3),(0,2),(0,5),(0,21)] hr rfl hshape middle_refuted
  intro i hi
  change i < 5 at hi
  interval_cases i
  · exact ⟨Nat.zero_le _,coreAlpha_le_21 p (by omega) (by omega)⟩
  · exact ⟨Nat.zero_le _,by simpa using h₂⟩
  · exact ⟨Nat.zero_le _,by simpa using h₃⟩
  · exact ⟨Nat.zero_le _,by simpa using h₄⟩
  · exact ⟨Nat.zero_le _,coreAlpha_le_21 p (by omega) (by omega)⟩

theorem actual_forward {m : Nat} (p : Snake m) (r s : Nat)
    (hr : r+9 ≤ m) (hs : s ≤ 1)
    (hshape : canon (((canon (dsOf p r 9)).drop (s+2)).take 6) = [0,1,2,3,4,0]) :
    ¬ intervalHit (sixCode p r) s 5 false [(0,21),(0,3),(0,2),(0,5),(0,21)] := by
  intro hhit
  exact encoded_interval_forward_exclusion p r s 5 hr (by omega) (by omega)
    [0,1,2,3,4,0] [(0,21),(0,3),(0,2),(0,5),(0,21)] rfl
    (by intro i hi;change i<5 at hi;interval_cases i <;> decide)
    middle_refuted hshape hhit

theorem actual_reverse {m : Nat} (p : Snake m) (r s : Nat)
    (hr : r+9 ≤ m) (hs : s ≤ 1)
    (hshape : canon ((((canon (dsOf p r 9)).drop (s+2)).take 6).reverse) = [0,1,2,3,4,0]) :
    ¬ intervalHit (sixCode p r) s 5 true [(0,21),(0,3),(0,2),(0,5),(0,21)] := by
  intro hhit
  exact encoded_interval_reverse_exclusion p r s 5 hr (by omega) (by omega)
    [0,1,2,3,4,0] [(0,21),(0,3),(0,2),(0,5),(0,21)] rfl
    (by intro i hi;change i<5 at hi;interval_cases i <;> decide)
    middle_refuted hshape hhit

#print axioms middle_refuted
#print axioms actual_three_counts
#print axioms actual_forward
#print axioms actual_reverse
#print axioms Snake9.LocalWindow.Middle325R.check
#print axioms Snake9.LocalWindow.Middle325R.sat
#print axioms Snake9.LocalWindow.Middle325R.unsat
end Snake9.MiddleCount111
