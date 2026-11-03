import ActualUniform124

/-!
Arithmetic consequences of the explicitly displayed local restrictions and of
retaining the empty-square count. The six-count floors 23 and 25 are not proved.
No new mathematical definition is introduced.
-/
namespace Snake9.Structural125
open Finset
open scoped BigOperators
open Snake9.LocalWindow Snake9.SquareIncidence

set_option maxHeartbeats 2000000

theorem six_sum_ge_seventeen (a b c d e f : Nat)
    (h13 : 5 ≤ a+c) (h24 : 8 ≤ b+d) (h56 : 4 ≤ e+f) :
    17 ≤ a+b+c+d+e+f := by omega

-- The added exclusion is the already proved consecutive triple (4,2,2).
theorem six_sum_ge_eighteen (a b c d e f : Nat)
    (h13 : 5 ≤ a+c) (h24 : 8 ≤ b+d) (h35 : 5 ≤ c+e)
    (h56 : 4 ≤ e+f) (he : 1 ≤ e) (hf : 1 ≤ f)
    (heone : e=1 → 4 ≤ f) (hfone : f=1 → 4 ≤ e)
    (h14 : ¬ (a ≤ 2 ∧ d ≤ 3)) (h25 : ¬ (b ≤ 3 ∧ e ≤ 2))
    (h422 : ¬ (d=4 ∧ e=2 ∧ f=2)) :
    18 ≤ a+b+c+d+e+f := by omega

theorem six_sum_ge_twenty_four_of_fourth_two (a b c d e f : Nat)
    (hd : d=2) (h14 : ¬ (a ≤ 2 ∧ d ≤ 3))
    (houter : 19 ≤ b+c+e+f) :
    24 ≤ a+b+c+d+e+f := by omega

-- T+D is used instead of truncated subtraction T >= m+748-D.
theorem deficit_required (m T D s : Nat) (hm : 235 ≤ m)
    (hcount : m+748 ≤ T+D)
    (hsquare : T+35*(m+1)+2*s ≤ 9214) :
    29+2*s ≤ D := by omega

theorem bound234_of_retained_deficit (m T D s : Nat)
    (hcount : 235 ≤ m → m+748 ≤ T+D)
    (hdef : D ≤ 28+2*s)
    (hsquare : T+35*(m+1)+2*s ≤ 9214) :
    m ≤ 234 := by
  by_contra h
  have hm : 235 ≤ m := by omega
  have hc := hcount hm
  have hd := deficit_required m T D s hm hc hsquare
  omega

theorem empty_at_most_thirteen (m T s : Nat) (hm : 234 ≤ m)
    (hcount : m+729 ≤ T)
    (hsquare : T+35*(m+1)+2*s ≤ 9214) : s ≤ 13 := by omega

-- This is the direct available interface: each ordinary empty square is
-- counted at all four corners by totalEmptyAnchored.
theorem retained_square_budget {m : Nat} (p : Snake m) (hm : 1 ≤ m) :
    4*(∑ i ∈ range (m+1), coreAlpha p i)+140*(m+1)+
      2*totalEmptyAnchored p ≤ 36856 := by
  rw [Snake9.GlobalCharge98.core_count_total p]
  have hi := global_identity p
  rw [selected_total p] at hi
  have hw := wedge_total_upper p
  omega

theorem total_with_thirty_nine_deficits (alpha : Nat → Nat) (m : Nat)
    (hm : 235 ≤ m)
    (h0 : 4 ≤ alpha 0) (hend : 4 ≤ alpha m)
    (hpos : ∀ i, 0 < i → i < m → 1 ≤ alpha i) :
    m+748 ≤ (∑ i ∈ range (m+1), alpha i)+
      ∑ b ∈ range 39, (25-∑ j ∈ range 6, alpha (6*b+j+1)) := by
  have hb := Snake9.SixDeficit124.blocks_with_deficits alpha 39 25
  norm_num at hb
  have hr : m-235 ≤ ∑ j ∈ range (m-235), alpha (234+j+1) := by
    calc
      _ = ∑ _j ∈ range (m-235), (1 : Nat) := by simp
      _ ≤ _ := Finset.sum_le_sum (by
        intro j hj
        have hj' := Finset.mem_range.mp hj
        exact hpos (234+j+1) (by omega) (by omega))
  have hs := Finset.sum_range_add (fun i => alpha (i+1)) 234 (m-235)
  have hl : 234+(m-235) = m-1 := by omega
  rw [hl] at hs
  have hp := Finset.sum_range_succ' alpha (m-1)
  have hm1 : m-1+1 = m := by omega
  rw [hm1] at hp
  have hpath : (∑ i ∈ range (m+1), alpha i) =
      alpha 0+(∑ i ∈ range (m-1), alpha (i+1))+alpha m := by
    rw [Finset.sum_range_succ, hp]
    omega
  omega

theorem actual_deficit_required {m : Nat} (p : Snake m) (hm : 235 ≤ m) :
    58+totalEmptyAnchored p ≤
      2*(∑ b ∈ range 39, (25-∑ j ∈ range 6, coreAlpha p (6*b+j+1))) := by
  obtain ⟨h0,hend,hpos,_⟩ := Snake9.ActualUniform124.count_bounds p (by omega)
  have hc := total_with_thirty_nine_deficits (coreAlpha p) m hm h0 hend hpos
  have hs := retained_square_budget p (by omega)
  omega

theorem actual_bound234_of_retained_deficit {m : Nat} (p : Snake m)
    (hdef : 235 ≤ m →
      2*(∑ b ∈ range 39, (25-∑ j ∈ range 6, coreAlpha p (6*b+j+1))) ≤
        56+totalEmptyAnchored p) : m ≤ 234 := by
  by_contra h
  have hm : 235 ≤ m := by omega
  have hd := actual_deficit_required p hm
  have hu := hdef hm
  omega

theorem actual_empty_at_most_fifty_two_of_floor25 {m : Nat} (p : Snake m)
    (hm : 234 ≤ m)
    (hfloor : ∀ r, 0 < r → r+5 < m →
      25 ≤ ∑ j ∈ range 6, coreAlpha p (r+j)) :
    totalEmptyAnchored p ≤ 52 := by
  obtain ⟨h0,hend,hpos,_⟩ := Snake9.ActualUniform124.count_bounds p (by omega)
  have hc := Snake9.UniformSix124.total_lower_of_six_floor
    (coreAlpha p) m 38 25 (by omega) h0 hend hpos hfloor
  norm_num at hc
  have hs := retained_square_budget p (by omega)
  omega

theorem actual_bound233_of_floor25_and_empty {m : Nat} (p : Snake m)
    (hfloor : ∀ r, 0 < r → r+5 < m →
      25 ≤ ∑ j ∈ range 6, coreAlpha p (r+j))
    (hempty : 234 ≤ m → 56 ≤ totalEmptyAnchored p) : m ≤ 233 := by
  by_contra h
  have hm : 234 ≤ m := by omega
  have hl := hempty hm
  have hu := actual_empty_at_most_fifty_two_of_floor25 p hm hfloor
  omega

#print axioms six_sum_ge_seventeen
#print axioms six_sum_ge_eighteen
#print axioms six_sum_ge_twenty_four_of_fourth_two
#print axioms deficit_required
#print axioms bound234_of_retained_deficit
#print axioms empty_at_most_thirteen
#print axioms retained_square_budget
#print axioms total_with_thirty_nine_deficits
#print axioms actual_deficit_required
#print axioms actual_bound234_of_retained_deficit
#print axioms actual_empty_at_most_fifty_two_of_floor25
#print axioms actual_bound233_of_floor25_and_empty
end Snake9.Structural125
