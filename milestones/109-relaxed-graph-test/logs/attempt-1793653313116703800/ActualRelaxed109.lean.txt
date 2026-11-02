import RelaxedReference108
import IntervalGuards

namespace Snake9.RelaxedGraph109
open Snake9.LocalWindow Snake9.WindowAutomaton Snake9.DirectionWindow
open Snake9.GraphInterpretation75 Snake9.GraphWalk78 Snake9.CountGeometry78
open Snake9.Guards79 Snake9.RecoveredReference108
set_option maxHeartbeats 2000000

theorem actual_three_counts {m : Nat} (p : Snake m) (r : Nat)
    (hr : r + 6 ≤ m)
    (hshape : canon (dsOf p r 6) = [0, 1, 2, 3, 0, 4]) :
    3 ≤ coreAlpha p (r+1) ∨ 3 ≤ coreAlpha p (r+4) ∨
      4 ≤ coreAlpha p (r+5) := by
  by_contra hn
  have h₁ : coreAlpha p (r+1) ≤ 2 := by omega
  have h₄ : coreAlpha p (r+4) ≤ 2 := by omega
  have h₅ : coreAlpha p (r+5) ≤ 3 := by omega
  apply canonical_interval_exclusion p r 6 [0, 1, 2, 3, 0, 4]
    [(0,2),(0,21),(0,21),(0,2),(0,3)] hr rfl hshape relaxed_reference_refuted
  intro i hi
  change i < 5 at hi
  interval_cases i
  · exact ⟨Nat.zero_le _, by simpa using h₁⟩
  · exact ⟨Nat.zero_le _, coreAlpha_le_21 p (by omega) (by omega)⟩
  · exact ⟨Nat.zero_le _, coreAlpha_le_21 p (by omega) (by omega)⟩
  · exact ⟨Nat.zero_le _, by simpa using h₄⟩
  · exact ⟨Nat.zero_le _, by simpa using h₅⟩

theorem actual_forward_retention {m : Nat} (p : Snake m) (r s : Nat)
    (hr : r+9 ≤ m) (hs : s ≤ 1)
    (hshape : canon (((canon (dsOf p r 9)).drop (s+2)).take 6) = [0,1,2,3,0,4]) :
    ¬ intervalHit (sixCode p r) s 5 false [(0,2),(0,21),(0,21),(0,2),(0,3)] := by
  intro hhit
  exact encoded_interval_forward_exclusion p r s 5 hr (by omega) (by omega)
    [0,1,2,3,0,4] [(0,2),(0,21),(0,21),(0,2),(0,3)] rfl
    (by intro i hi; change i < 5 at hi; interval_cases i <;> decide)
    relaxed_reference_refuted hshape hhit

theorem actual_reverse_retention {m : Nat} (p : Snake m) (r s : Nat)
    (hr : r+9 ≤ m) (hs : s ≤ 1)
    (hshape : canon ((((canon (dsOf p r 9)).drop (s+2)).take 6).reverse) = [0,1,2,3,0,4]) :
    ¬ intervalHit (sixCode p r) s 5 true [(0,2),(0,21),(0,21),(0,2),(0,3)] := by
  intro hhit
  exact encoded_interval_reverse_exclusion p r s 5 hr (by omega) (by omega)
    [0,1,2,3,0,4] [(0,2),(0,21),(0,21),(0,2),(0,3)] rfl
    (by intro i hi; change i < 5 at hi; interval_cases i <;> decide)
    relaxed_reference_refuted hshape hhit

#print axioms actual_three_counts
#print axioms actual_forward_retention
#print axioms actual_reverse_retention
end Snake9.RelaxedGraph109
