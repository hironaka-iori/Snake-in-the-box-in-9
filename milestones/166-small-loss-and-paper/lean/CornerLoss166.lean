import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
namespace Snake9.CornerLoss166
-- The geometric hypothesis is the number of available pairs of absent neighbours.
theorem degree_decomposition (d e : ℕ) (hd : d ≤ 9)
    (he : e ≤ (9 - d) * (8 - d) / 2) :
    (if d = 0 then 12 * e else (12 * e) % d) =
    (if d = 0 then 12 * e else if d = 5 then (2 * e) % 5
      else if d = 7 then 5 * e else 0) := by
  interval_cases d <;> norm_num at * <;> omega

theorem degree_five_table (e : ℕ) (he : e ≤ 6) :
    (2 * e) % 5 =
      (if e = 1 ∨ e = 6 then 2 else if e = 2 then 4
       else if e = 3 then 1 else if e = 4 then 3 else 0) := by
  interval_cases e <;> norm_num

theorem small_loss_zero_degree (e loss : ℕ)
    (h : 12 * e ≤ loss) (hl : loss ≤ 3) : e = 0 := by omega

theorem small_loss_degree_seven (e loss : ℕ)
    (h : 5 * e ≤ loss) (hl : loss ≤ 3) : e = 0 := by omega

theorem small_loss_degree_five (e loss : ℕ) (he : e ≤ 6)
    (h : (2 * e) % 5 ≤ loss) (hl : loss ≤ 3) : e ≠ 2 := by omega

theorem zero_loss_degree_five (e : ℕ) (he : e ≤ 6)
    (h : (2 * e) % 5 = 0) : e = 0 ∨ e = 5 := by omega

#print axioms degree_decomposition
#print axioms degree_five_table
#print axioms small_loss_zero_degree
#print axioms small_loss_degree_seven
#print axioms small_loss_degree_five
#print axioms zero_loss_degree_five
end Snake9.CornerLoss166
