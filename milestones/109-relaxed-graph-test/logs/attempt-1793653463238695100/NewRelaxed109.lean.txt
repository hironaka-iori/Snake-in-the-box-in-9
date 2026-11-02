import Recovered109.LocalWindowSat.D01234A1542
import Recovered109.LocalWindowUnsat.D01234A1542
import ActualRelaxed109

namespace Snake9.RelaxedGraph109
open Snake9.LocalWindow Snake9.WindowAutomaton Snake9.DirectionWindow
open Snake9.GraphInterpretation75 Snake9.GraphWalk78 Snake9.CountGeometry78
open Snake9.Guards79
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem relaxed_01234_refuted :
    Refuted (winOf [0,1,2,3,4]) [(0,1),(0,5),(0,21),(0,2)] := by
  let cs : List Tags.Ctr := D01234A1542.ctrs.mapIdx fun i ct =>
    if i ∈ [2,4,5,6,8] then { ct with k := 21 } else ct
  have hc : Tags.checkAll D01234A1542.meaning cs D01234A1542.window
      [(0,1),(0,5),(0,21),(0,2)] D01234A1542.tags D01234A1542.raw = true := by
    decide +kernel
  apply Tags.refuted_of_sat (f := D01234A1542.cnf) ?_ D01234A1542.unsat
  intro S E h
  exact ⟨Tags.tau S E D01234A1542.meaning cs,
    Tags.sound D01234A1542.meaning cs D01234A1542.window
      [(0,1),(0,5),(0,21),(0,2)] D01234A1542.tags D01234A1542.raw hc S E h⟩

theorem actual_01234_counts {m : Nat} (p : Snake m) (r : Nat)
    (hr : r+5 ≤ m)
    (hshape : canon (dsOf p r 5) = [0,1,2,3,4]) :
    2 ≤ coreAlpha p (r+1) ∨ 6 ≤ coreAlpha p (r+2) ∨
      3 ≤ coreAlpha p (r+4) := by
  by_contra hn
  have h₁ : coreAlpha p (r+1) ≤ 1 := by omega
  have h₂ : coreAlpha p (r+2) ≤ 5 := by omega
  have h₄ : coreAlpha p (r+4) ≤ 2 := by omega
  apply canonical_interval_exclusion p r 5 [0,1,2,3,4]
    [(0,1),(0,5),(0,21),(0,2)] hr rfl hshape relaxed_01234_refuted
  intro i hi
  change i < 4 at hi
  interval_cases i
  · exact ⟨Nat.zero_le _, by simpa using h₁⟩
  · exact ⟨Nat.zero_le _, by simpa using h₂⟩
  · exact ⟨Nat.zero_le _, coreAlpha_le_21 p (by omega) (by omega)⟩
  · exact ⟨Nat.zero_le _, by simpa using h₄⟩

theorem actual_01234_forward {m : Nat} (p : Snake m) (r s : Nat)
    (hr : r+9 ≤ m) (hs : s ≤ 2)
    (hshape : canon (((canon (dsOf p r 9)).drop (s+2)).take 5) = [0,1,2,3,4]) :
    ¬ intervalHit (sixCode p r) s 4 false [(0,1),(0,5),(0,21),(0,2)] := by
  intro hhit
  exact encoded_interval_forward_exclusion p r s 4 hr (by omega) (by omega)
    [0,1,2,3,4] [(0,1),(0,5),(0,21),(0,2)] rfl
    (by intro i hi; change i < 4 at hi; interval_cases i <;> decide)
    relaxed_01234_refuted hshape hhit

theorem actual_01234_reverse {m : Nat} (p : Snake m) (r s : Nat)
    (hr : r+9 ≤ m) (hs : s ≤ 2)
    (hshape : canon ((((canon (dsOf p r 9)).drop (s+2)).take 5).reverse) = [0,1,2,3,4]) :
    ¬ intervalHit (sixCode p r) s 4 true [(0,1),(0,5),(0,21),(0,2)] := by
  intro hhit
  exact encoded_interval_reverse_exclusion p r s 4 hr (by omega) (by omega)
    [0,1,2,3,4] [(0,1),(0,5),(0,21),(0,2)] rfl
    (by intro i hi; change i < 4 at hi; interval_cases i <;> decide)
    relaxed_01234_refuted hshape hhit

#print axioms relaxed_01234_refuted
#print axioms actual_01234_counts
#print axioms actual_01234_forward
#print axioms actual_01234_reverse
#print axioms Snake9.LocalWindow.D01234A1542.check
#print axioms Snake9.LocalWindow.D01234A1542.sat
#print axioms Snake9.LocalWindow.D01234A1542.unsat
#print axioms Snake9.LocalWindow.D01234A1542.ok1
end Snake9.RelaxedGraph109
