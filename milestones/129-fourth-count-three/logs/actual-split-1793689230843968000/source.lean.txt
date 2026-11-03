import ActualBounds125

namespace Snake9.ActualSplit129
open Finset
open scoped BigOperators
open Snake9.LocalWindow Snake9.WindowAutomaton Snake9.DirectionWindow

set_option maxHeartbeats 2000000

theorem actual_fourth_split {m : Nat} (p : Snake m) (r : Nat)
    (hr : r+7 ≤ m)
    (hshape : canon (dsOf p r 7) = [0,1,2,0,3,2,4])
    (htotal : (∑ j ∈ range 6, coreAlpha p (r+j+1)) ≤ 22) :
    coreAlpha p (r+4) = 3 ∨ 4 ≤ coreAlpha p (r+4) := by
  have h := (ActualBounds125.second_fourth_minima_of_total22 p r hr hshape htotal).2
  omega

theorem actual_equality_consequences {m : Nat} (p : Snake m) (r : Nat)
    (hr : r+7 ≤ m)
    (hshape : canon (dsOf p r 7) = [0,1,2,0,3,2,4])
    (htotal : (∑ j ∈ range 6, coreAlpha p (r+j+1)) ≤ 22)
    (hfourth : coreAlpha p (r+4) = 3) :
    3 ≤ coreAlpha p (r+1) ∧ 5 ≤ coreAlpha p (r+2) ∧
      coreAlpha p (r+3)+coreAlpha p (r+5)+coreAlpha p (r+6) ≤ 11 := by
  have hp := (ActualBounds125.prefix_and_suffix p r hr hshape).1
  have h14 := ActualBounds125.first_fourth_exclusion p r (by omega) hp
  have hpair := ActualPair121.actual_pair_sum p r (by omega) hp
  have h1 : 3 ≤ coreAlpha p (r+1) := by omega
  have h2 : 5 ≤ coreAlpha p (r+2) := by omega
  have ht : coreAlpha p (r+1)+coreAlpha p (r+2)+coreAlpha p (r+3)+
      coreAlpha p (r+4)+coreAlpha p (r+5)+coreAlpha p (r+6) ≤ 22 := by
    simpa [Finset.sum_range_succ, Nat.add_assoc] using htotal
  exact ⟨h1,h2,by omega⟩

theorem actual_equality_bounds {m : Nat} (p : Snake m) (r : Nat)
    (hr : r+7 ≤ m)
    (hshape : canon (dsOf p r 7) = [0,1,2,0,3,2,4])
    (htotal : (∑ j ∈ range 6, coreAlpha p (r+j+1)) ≤ 22)
    (hfourth : coreAlpha p (r+4) = 3) :
    ∀ i, i < 6 →
      (([(3,21),(5,21),(1,21),(3,3),(1,21),(1,21)] : List (Nat × Nat)).getD
        i (0,21)).1 ≤ coreAlpha p (r+i+1) ∧
      coreAlpha p (r+i+1) ≤
        (([(3,21),(5,21),(1,21),(3,3),(1,21),(1,21)] : List (Nat × Nat)).getD
          i (0,21)).2 := by
  have hc := actual_equality_consequences p r hr hshape htotal hfourth
  intro i hi
  have hb := ActualBounds125.actual_six_bounds p r hr hshape htotal i hi
  interval_cases i <;> simp_all [Nat.add_assoc]

theorem actual_large_bounds {m : Nat} (p : Snake m) (r : Nat)
    (hr : r+7 ≤ m)
    (hshape : canon (dsOf p r 7) = [0,1,2,0,3,2,4])
    (htotal : (∑ j ∈ range 6, coreAlpha p (r+j+1)) ≤ 22)
    (hfourth : 4 ≤ coreAlpha p (r+4)) :
    ∀ i, i < 6 →
      (([(1,21),(2,21),(1,21),(4,21),(1,21),(1,21)] : List (Nat × Nat)).getD
        i (0,21)).1 ≤ coreAlpha p (r+i+1) ∧
      coreAlpha p (r+i+1) ≤
        (([(1,21),(2,21),(1,21),(4,21),(1,21),(1,21)] : List (Nat × Nat)).getD
          i (0,21)).2 := by
  intro i hi
  have hb := ActualBounds125.actual_six_bounds p r hr hshape htotal i hi
  interval_cases i <;> simp_all [Nat.add_assoc]

-- These are the two exhaustive sets of necessary conditions for a total22 window.
theorem actual_exhaustive_bounds {m : Nat} (p : Snake m) (r : Nat)
    (hr : r+7 ≤ m)
    (hshape : canon (dsOf p r 7) = [0,1,2,0,3,2,4])
    (htotal : (∑ j ∈ range 6, coreAlpha p (r+j+1)) ≤ 22) :
    ((∀ i, i < 6 →
      (([(3,21),(5,21),(1,21),(3,3),(1,21),(1,21)] : List (Nat × Nat)).getD
        i (0,21)).1 ≤ coreAlpha p (r+i+1) ∧
      coreAlpha p (r+i+1) ≤
        (([(3,21),(5,21),(1,21),(3,3),(1,21),(1,21)] : List (Nat × Nat)).getD
          i (0,21)).2) ∧
      coreAlpha p (r+3)+coreAlpha p (r+5)+coreAlpha p (r+6) ≤ 11) ∨
    (∀ i, i < 6 →
      (([(1,21),(2,21),(1,21),(4,21),(1,21),(1,21)] : List (Nat × Nat)).getD
        i (0,21)).1 ≤ coreAlpha p (r+i+1) ∧
      coreAlpha p (r+i+1) ≤
        (([(1,21),(2,21),(1,21),(4,21),(1,21),(1,21)] : List (Nat × Nat)).getD
          i (0,21)).2) := by
  rcases actual_fourth_split p r hr hshape htotal with heq | hlarge
  · exact Or.inl ⟨actual_equality_bounds p r hr hshape htotal heq,
      (actual_equality_consequences p r hr hshape htotal heq).2.2⟩
  · exact Or.inr (actual_large_bounds p r hr hshape htotal hlarge)

#print axioms actual_fourth_split
#print axioms actual_equality_consequences
#print axioms actual_equality_bounds
#print axioms actual_large_bounds
#print axioms actual_exhaustive_bounds
end Snake9.ActualSplit129
