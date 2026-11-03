import ActualPair121
import ActualSum112
import CycleExclusion4906

namespace Snake9.ActualBounds125
open Finset
open scoped BigOperators
open Snake9.LocalWindow Snake9.WindowAutomaton Snake9.DirectionWindow
open Snake9.Guards79 Snake9.GraphWalk78 Snake9.CountGeometry78

set_option maxHeartbeats 2000000

theorem canonical_seven_slice {m : Nat} (p : Snake m) (r s w : Nat)
    (hr : r+7 ≤ m) (hs : s+w ≤ 7) :
    canon (((canon (dsOf p r 7)).drop s).take w) =
      canon (dsOf p (r+s) w) := by
  rw [← canon_canon_take, canon_canon_drop, canon_canon_take,
    Snake9.GraphInterpretation74.dsOf_slice p r 7 s w hr hs]

theorem prefix_and_suffix {m : Nat} (p : Snake m) (r : Nat)
    (hr : r+7 ≤ m)
    (hshape : canon (dsOf p r 7) = [0,1,2,0,3,2,4]) :
    canon (dsOf p r 6) = [0,1,2,0,3,2] ∧
    canon (dsOf p (r+1) 6) = [0,1,2,3,1,4] := by
  have hp := canonical_seven_slice p r 0 6 hr (by decide)
  have hs := canonical_seven_slice p r 1 6 hr (by decide)
  rw [hshape] at hp hs
  have cp : canon ((([0,1,2,0,3,2,4] : List Nat).drop 0).take 6) =
      [0,1,2,0,3,2] := by decide
  have cs : canon ((([0,1,2,0,3,2,4] : List Nat).drop 1).take 6) =
      [0,1,2,3,1,4] := by decide
  rw [cp] at hp
  rw [cs] at hs
  exact ⟨by simpa using hp.symm, hs.symm⟩

-- This is the saved h14 pair-cap exclusion, transported canonically.
theorem first_fourth_exclusion {m : Nat} (p : Snake m) (r : Nat)
    (hr : r+6 ≤ m)
    (hshape : canon (dsOf p r 6) = [0,1,2,0,3,2]) :
    ¬ (coreAlpha p (r+1) ≤ 2 ∧ coreAlpha p (r+4) ≤ 3) := by
  intro h
  have href : Refuted (winOf [0,1,2,0,3,2])
      [(0,2),(0,21),(0,21),(0,3),(0,21)] := CycleWindow4906.refuted
  apply canonical_interval_exclusion p r 6 [0,1,2,0,3,2]
    [(0,2),(0,21),(0,21),(0,3),(0,21)] hr rfl hshape href
  intro i hi
  change i < 5 at hi
  interval_cases i
  · exact ⟨Nat.zero_le _,by simpa using h.1⟩
  · exact ⟨Nat.zero_le _,coreAlpha_le_21 p (by omega) (by omega)⟩
  · exact ⟨Nat.zero_le _,coreAlpha_le_21 p (by omega) (by omega)⟩
  · exact ⟨Nat.zero_le _,by simpa using h.2⟩
  · exact ⟨Nat.zero_le _,coreAlpha_le_21 p (by omega) (by omega)⟩

theorem second_fourth_minima_of_total22 {m : Nat} (p : Snake m) (r : Nat)
    (hr : r+7 ≤ m)
    (hshape : canon (dsOf p r 7) = [0,1,2,0,3,2,4])
    (htotal : (∑ j ∈ range 6, coreAlpha p (r+j+1)) ≤ 22) :
    2 ≤ coreAlpha p (r+2) ∧ 3 ≤ coreAlpha p (r+4) := by
  obtain ⟨hp,hs⟩ := prefix_and_suffix p r hr hshape
  obtain ⟨h2,h4⟩ := Snake9.ActualPair121.actual_pair_minima p r (by omega) hp
  refine ⟨h2, ?_⟩
  by_contra hn
  have hsmall : coreAlpha p (r+4) ≤ 2 := by omega
  have h14 := first_fourth_exclusion p r (by omega) hp
  have hfirst : 3 ≤ coreAlpha p (r+1) := by omega
  have hout := Snake9.ActualSum112.actual_outer_sum p (r+1) (by omega) hs
    (by simpa [Nat.add_assoc] using hsmall)
  have ht : coreAlpha p (r+1)+coreAlpha p (r+2)+coreAlpha p (r+3)+
      coreAlpha p (r+4)+coreAlpha p (r+5)+coreAlpha p (r+6) ≤ 22 := by
    simpa [Finset.sum_range_succ, Nat.add_assoc] using htotal
  norm_num only [Nat.add_assoc] at hout
  omega

theorem actual_six_bounds {m : Nat} (p : Snake m) (r : Nat)
    (hr : r+7 ≤ m)
    (hshape : canon (dsOf p r 7) = [0,1,2,0,3,2,4])
    (htotal : (∑ j ∈ range 6, coreAlpha p (r+j+1)) ≤ 22) :
    ∀ i, i < 6 →
      (([(1,21),(2,21),(1,21),(3,21),(1,21),(1,21)] : List (Nat × Nat)).getD
        i (0,21)).1 ≤ coreAlpha p (r+i+1) ∧
      coreAlpha p (r+i+1) ≤
        (([(1,21),(2,21),(1,21),(3,21),(1,21),(1,21)] : List (Nat × Nat)).getD
          i (0,21)).2 := by
  obtain ⟨h2,h4⟩ := second_fourth_minima_of_total22 p r hr hshape htotal
  intro i hi
  have hl := core_count_positive p (r+i+1) (by omega)
  have hu := coreAlpha_le_21 p (k := r+i+1) (by omega) (by omega)
  interval_cases i <;> simp_all [Nat.add_assoc]

#print axioms canonical_seven_slice
#print axioms prefix_and_suffix
#print axioms first_fourth_exclusion
#print axioms second_fourth_minima_of_total22
#print axioms actual_six_bounds
end Snake9.ActualBounds125
