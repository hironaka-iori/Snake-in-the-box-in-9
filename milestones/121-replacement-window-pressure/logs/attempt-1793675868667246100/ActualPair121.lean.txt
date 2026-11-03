import Recovered121G.LocalWindowSat.PairMin032
import Recovered121G.LocalWindowUnsat.PairMin032
import Recovered121G.LocalWindowSat.Pair25032
import Recovered121G.LocalWindowUnsat.Pair25032
import Recovered121G.LocalWindowSat.Pair34032
import Recovered121G.LocalWindowUnsat.Pair34032
import ReferenceInterface

namespace Snake9.ActualPair121
open Snake9.LocalWindow Snake9.WindowAutomaton Snake9.DirectionWindow
open Snake9.GraphInterpretation75 Snake9.GraphWalk78 Snake9.CountGeometry78
open Snake9.Guards79
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem minimum_refuted :
    Refuted (winOf [0,1,2,0,3,2])
      [(0,21),(0,1),(0,21),(0,21),(0,21)] :=
  Tags.refuted_of_sat PairMin032.sat PairMin032.unsat

theorem pair25_refuted :
    Refuted (winOf [0,1,2,0,3,2])
      [(0,21),(0,2),(0,21),(0,5),(0,21)] :=
  Tags.refuted_of_sat Pair25032.sat Pair25032.unsat

theorem pair34_refuted :
    Refuted (winOf [0,1,2,0,3,2])
      [(0,21),(0,3),(0,21),(0,4),(0,21)] :=
  Tags.refuted_of_sat Pair34032.sat Pair34032.unsat

theorem actual_pair_exclusion {m : Nat} (p : Snake m) (r a b : Nat)
    (hr : r+6 ≤ m)
    (hshape : canon (dsOf p r 6) = [0,1,2,0,3,2])
    (href : Refuted (winOf [0,1,2,0,3,2])
      [(0,21),(0,a),(0,21),(0,b),(0,21)]) :
    ¬ (coreAlpha p (r+2) ≤ a ∧ coreAlpha p (r+4) ≤ b) := by
  intro hab
  apply canonical_interval_exclusion p r 6 [0,1,2,0,3,2]
    [(0,21),(0,a),(0,21),(0,b),(0,21)] hr rfl hshape href
  intro i hi
  change i < 5 at hi
  interval_cases i
  · exact ⟨Nat.zero_le _,coreAlpha_le_21 p (by omega) (by omega)⟩
  · exact ⟨Nat.zero_le _,by simpa using hab.1⟩
  · exact ⟨Nat.zero_le _,coreAlpha_le_21 p (by omega) (by omega)⟩
  · exact ⟨Nat.zero_le _,by simpa using hab.2⟩
  · exact ⟨Nat.zero_le _,coreAlpha_le_21 p (by omega) (by omega)⟩

theorem actual_reversed_pair_exclusion {m : Nat} (p : Snake m) (r a b : Nat)
    (hr : r+6 ≤ m)
    (hshape : canon (dsOf p r 6) = [0,1,2,0,3,2])
    (href : Refuted (winOf [0,1,2,0,3,2])
      [(0,21),(0,a),(0,21),(0,b),(0,21)]) :
    ¬ (coreAlpha p (r+4) ≤ a ∧ coreAlpha p (r+2) ≤ b) := by
  have hs : canon (dsOf (revSnake p) (m-r-6) 6) = [0,1,2,0,3,2] := by
    rw [dsOf_rev p r 6 hr, ← reverse_canon, hshape]
    rfl
  have h := actual_pair_exclusion (revSnake p) (m-r-6) a b (by omega) hs href
  intro hab
  apply h
  constructor
  · rw [coreAlpha_rev p (by omega)]
    have hi : m-(m-r-6+2) = r+4 := by omega
    simpa only [hi] using hab.1
  · rw [coreAlpha_rev p (by omega)]
    have hi : m-(m-r-6+4) = r+2 := by omega
    simpa only [hi] using hab.2

theorem actual_pair_minima {m : Nat} (p : Snake m) (r : Nat)
    (hr : r+6 ≤ m)
    (hshape : canon (dsOf p r 6) = [0,1,2,0,3,2]) :
    2 ≤ coreAlpha p (r+2) ∧ 2 ≤ coreAlpha p (r+4) := by
  have h := actual_pair_exclusion p r 1 21 hr hshape minimum_refuted
  have hrev := actual_reversed_pair_exclusion p r 1 21 hr hshape minimum_refuted
  have h₂ := coreAlpha_le_21 p (by omega : 0 < r+2) (by omega : r+2 < m)
  have h₄ := coreAlpha_le_21 p (by omega : 0 < r+4) (by omega : r+4 < m)
  omega

theorem actual_pair_sum {m : Nat} (p : Snake m) (r : Nat)
    (hr : r+6 ≤ m)
    (hshape : canon (dsOf p r 6) = [0,1,2,0,3,2]) :
    8 ≤ coreAlpha p (r+2) + coreAlpha p (r+4) := by
  have hmin := actual_pair_minima p r hr hshape
  have h25 := actual_pair_exclusion p r 2 5 hr hshape pair25_refuted
  have h52 := actual_reversed_pair_exclusion p r 2 5 hr hshape pair25_refuted
  have h34 := actual_pair_exclusion p r 3 4 hr hshape pair34_refuted
  have h43 := actual_reversed_pair_exclusion p r 3 4 hr hshape pair34_refuted
  omega

theorem actual_forward {m : Nat} (p : Snake m) (r s a b : Nat)
    (hr : r+9 ≤ m) (hs : s ≤ 1)
    (ha : a < 6 ∨ a = 21) (hb : b < 6 ∨ b = 21)
    (href : Refuted (winOf [0,1,2,0,3,2])
      [(0,21),(0,a),(0,21),(0,b),(0,21)])
    (hshape : canon (((canon (dsOf p r 9)).drop (s+2)).take 6) = [0,1,2,0,3,2]) :
    ¬ intervalHit (sixCode p r) s 5 false [(0,21),(0,a),(0,21),(0,b),(0,21)] := by
  intro hhit
  exact encoded_interval_forward_exclusion p r s 5 hr (by omega) (by omega)
    [0,1,2,0,3,2] [(0,21),(0,a),(0,21),(0,b),(0,21)] rfl
    (by intro i hi; change i<5 at hi; interval_cases i <;> simp [ha,hb])
    href hshape hhit

theorem actual_reverse {m : Nat} (p : Snake m) (r s a b : Nat)
    (hr : r+9 ≤ m) (hs : s ≤ 1)
    (ha : a < 6 ∨ a = 21) (hb : b < 6 ∨ b = 21)
    (href : Refuted (winOf [0,1,2,0,3,2])
      [(0,21),(0,a),(0,21),(0,b),(0,21)])
    (hshape : canon ((((canon (dsOf p r 9)).drop (s+2)).take 6).reverse) = [0,1,2,0,3,2]) :
    ¬ intervalHit (sixCode p r) s 5 true [(0,21),(0,a),(0,21),(0,b),(0,21)] := by
  intro hhit
  exact encoded_interval_reverse_exclusion p r s 5 hr (by omega) (by omega)
    [0,1,2,0,3,2] [(0,21),(0,a),(0,21),(0,b),(0,21)] rfl
    (by intro i hi; change i<5 at hi; interval_cases i <;> simp [ha,hb])
    href hshape hhit

#print axioms minimum_refuted
#print axioms pair25_refuted
#print axioms pair34_refuted
#print axioms actual_pair_exclusion
#print axioms actual_reversed_pair_exclusion
#print axioms actual_pair_minima
#print axioms actual_pair_sum
#print axioms actual_forward
#print axioms actual_reverse
#print axioms Snake9.LocalWindow.PairMin032.check
#print axioms Snake9.LocalWindow.PairMin032.sat
#print axioms Snake9.LocalWindow.PairMin032.unsat
#print axioms Snake9.LocalWindow.Pair25032.check
#print axioms Snake9.LocalWindow.Pair25032.sat
#print axioms Snake9.LocalWindow.Pair25032.unsat
#print axioms Snake9.LocalWindow.Pair34032.check
#print axioms Snake9.LocalWindow.Pair34032.sat
#print axioms Snake9.LocalWindow.Pair34032.unsat
end Snake9.ActualPair121
