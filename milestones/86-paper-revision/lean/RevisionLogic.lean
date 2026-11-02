import Mathlib.Tactic

namespace Snake9.Revision86

theorem cycle_family_unchanged {C : Type*} (cost bonus length : C → ℚ)
    (mean : ℚ) (witness : C)
    (hlower : ∀ c, mean * length c ≤ cost c)
    (hbonus : ∀ c, 0 ≤ bonus c)
    (hattains : cost witness = mean * length witness)
    (hzero : bonus witness = 0) :
    (∀ c, mean * length c ≤ cost c + bonus c) ∧
      cost witness + bonus witness = mean * length witness := by
  constructor
  · intro c
    exact le_trans (hlower c) (le_add_of_nonneg_right (hbonus c))
  · rw [hzero, add_zero, hattains]

theorem cycle_bonus_nonnegative (n : Nat) (bonus : Fin n → ℚ)
    (h : ∀ i, 0 ≤ bonus i) : 0 ≤ ∑ i, bonus i :=
  Finset.sum_nonneg (fun i _ => h i)

theorem cycle_bonus_zero (n : Nat) (bonus : Fin n → ℚ)
    (h : ∀ i, bonus i = 0) : (∑ i, bonus i) = 0 := by
  simp only [h, Finset.sum_const_zero]

theorem completed_share_comparison (m W : Nat) (hm : 8 ≤ m)
    (hbudget : W + 4200*m ≤ 1098960)
    (hpotential : 483*(m-8) ≤ W+551) : m ≤ 235 := by
  omega

theorem single_target_comparison (m W : Nat) (hm : 8 ≤ m)
    (hbudget : W + 4200*m ≤ 1098960)
    (hpotential : 9259*(m-8) ≤ 19*W+11301) : m ≤ 235 := by
  omega

theorem full_target_comparison (m W : Nat) (hm : 8 ≤ m)
    (hbudget : W + 4200*m ≤ 1098960)
    (hpotential : 496*(m-8) ≤ W+600) : m ≤ 234 := by
  omega

theorem four_comparison_fractions :
    (1098960+8*480+536 : ℚ)/(4200+480) = 10609/45 ∧
    (1098960+8*483+551 : ℚ)/(4200+483) = 157625/669 ∧
    (1098960*19+8*9259+11301 : ℚ)/(4200*19+9259) = 20965613/89059 ∧
    (1098960+8*496+600 : ℚ)/(4200+496) = 137941/587 := by
  norm_num

#print axioms cycle_family_unchanged
#print axioms cycle_bonus_nonnegative
#print axioms cycle_bonus_zero
#print axioms completed_share_comparison
#print axioms single_target_comparison
#print axioms full_target_comparison
#print axioms four_comparison_fractions
end Snake9.Revision86
