import Recovered121G.LocalWindowSat.Lower032
import Recovered121G.LocalWindowUnsat.Lower032
import ReferenceInterface

namespace Snake9.ActualOuter121
open Snake9.LocalWindow Snake9.WindowAutomaton Snake9.DirectionWindow
open Snake9.GraphInterpretation75 Snake9.GraphWalk78 Snake9.CountGeometry78
open Snake9.Guards79
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem outer_refuted :
    Refuted (winOf [0,1,2,0,3,2])
      [(0,4),(0,3),(0,21),(0,4),(0,4)] :=
  Tags.refuted_of_sat Lower032.sat Lower032.unsat

theorem actual_outer_counts {m : Nat} (p : Snake m) (r : Nat)
    (hr : r+6 ≤ m)
    (hshape : canon (dsOf p r 6) = [0,1,2,0,3,2]) :
    5 ≤ coreAlpha p (r+1) ∨ 4 ≤ coreAlpha p (r+2) ∨
      5 ≤ coreAlpha p (r+4) ∨ 5 ≤ coreAlpha p (r+5) := by
  by_contra hn
  have h₁ : coreAlpha p (r+1) ≤ 4 := by omega
  have h₂ : coreAlpha p (r+2) ≤ 3 := by omega
  have h₄ : coreAlpha p (r+4) ≤ 4 := by omega
  have h₅ : coreAlpha p (r+5) ≤ 4 := by omega
  apply canonical_interval_exclusion p r 6 [0,1,2,0,3,2]
    [(0,4),(0,3),(0,21),(0,4),(0,4)] hr rfl hshape outer_refuted
  intro i hi
  change i < 5 at hi
  interval_cases i
  · exact ⟨Nat.zero_le _,by simpa using h₁⟩
  · exact ⟨Nat.zero_le _,by simpa using h₂⟩
  · exact ⟨Nat.zero_le _,coreAlpha_le_21 p (by omega) (by omega)⟩
  · exact ⟨Nat.zero_le _,by simpa using h₄⟩
  · exact ⟨Nat.zero_le _,by simpa using h₅⟩

theorem actual_forward {m : Nat} (p : Snake m) (r s : Nat)
    (hr : r+9 ≤ m) (hs : s ≤ 1)
    (hshape : canon (((canon (dsOf p r 9)).drop (s+2)).take 6) = [0,1,2,0,3,2]) :
    ¬ intervalHit (sixCode p r) s 5 false [(0,4),(0,3),(0,21),(0,4),(0,4)] := by
  intro hhit
  exact encoded_interval_forward_exclusion p r s 5 hr (by omega) (by omega)
    [0,1,2,0,3,2] [(0,4),(0,3),(0,21),(0,4),(0,4)] rfl
    (by intro i hi;change i<5 at hi;interval_cases i <;> decide)
    outer_refuted hshape hhit

theorem actual_reverse {m : Nat} (p : Snake m) (r s : Nat)
    (hr : r+9 ≤ m) (hs : s ≤ 1)
    (hshape : canon ((((canon (dsOf p r 9)).drop (s+2)).take 6).reverse) = [0,1,2,0,3,2]) :
    ¬ intervalHit (sixCode p r) s 5 true [(0,4),(0,3),(0,21),(0,4),(0,4)] := by
  intro hhit
  exact encoded_interval_reverse_exclusion p r s 5 hr (by omega) (by omega)
    [0,1,2,0,3,2] [(0,4),(0,3),(0,21),(0,4),(0,4)] rfl
    (by intro i hi;change i<5 at hi;interval_cases i <;> decide)
    outer_refuted hshape hhit

#print axioms outer_refuted
#print axioms actual_outer_counts
#print axioms actual_forward
#print axioms actual_reverse
#print axioms Snake9.LocalWindow.Lower032.check
#print axioms Snake9.LocalWindow.Lower032.sat
#print axioms Snake9.LocalWindow.Lower032.unsat
end Snake9.ActualOuter121
