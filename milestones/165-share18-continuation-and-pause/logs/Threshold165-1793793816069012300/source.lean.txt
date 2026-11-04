import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
namespace Snake9.Threshold165
 theorem scaled_comparison (r : ℚ) :
    (9926156 + r) / 42262 < 235 ↔ r < 5414 := by
  rw [div_lt_iff₀ (by norm_num : (0 : ℚ) < 42262)]
  constructor <;> intro h <;> linarith
 theorem integer_edge_bound (m r : ℕ)
    (h : 42262 * m ≤ 9926156 + r) (hr : r ≤ 5413) : m ≤ 234 := by
  omega
 theorem saved_walks :
    (9 * 4462 - 9 * 3861 : ℤ) = 5409 ∧
    (149 * 4462 - 9 * 73271 : ℤ) = 5399 := by norm_num
 theorem attained_comparison :
    (4462 * 35 - 9 * 16751 : ℤ) = 5411 ∧
    (9926156 + 5411 : ℚ) / 42262 = 235 - 3 / 42262 := by norm_num
 theorem conditional_edge_bound (m : ℕ)
    (h : (42262 : ℚ) * m ≤ 9926156 + 5411) : m ≤ 234 := by
  by_contra hm
  have hi : 235 ≤ m := by omega
  have hq : (235 : ℚ) ≤ m := by exact_mod_cast hi
  linarith
#print axioms attained_comparison
#print axioms conditional_edge_bound
#print axioms scaled_comparison
#print axioms integer_edge_bound
#print axioms saved_walks
end Snake9.Threshold165
