import ShareLoss172

namespace Snake9.Critical173
open SquareIncidence Count171 Integration172
open scoped BigOperators

-- W is the integer weight of the retained windows; the premises remain explicit.
theorem critical_loss_at_most_three {m : Nat} (p : Snake m) (hm : 235 ≤ m)
    (W : Nat)
    (hpacking : W + 2520 ≤ 5 *
      (24 * totalSingleton p + ∑ x, selected p x * shareN 12 p x))
    (hpotential : 4462 * (m-8) ≤ 9 * W + 5411) : totalLoss p ≤ 3 := by
  have hb := charge_budget_with_loss p (by omega)
  omega

theorem critical_dominates {m : Nat} (p : Snake m) (hm : 235 ≤ m)
    (W : Nat)
    (hpacking : W + 2520 ≤ 5 *
      (24 * totalSingleton p + ∑ x, selected p x * shareN 12 p x))
    (hpotential : 4462 * (m-8) ≤ 9 * W + 5411) :
    ∀ q : Vertex, ∃ v, InPath p v ∧ Adj q v := by
  have hl := critical_loss_at_most_three p hm W hpacking hpotential
  exact small_loss_dominates p (by omega) (by omega)

theorem conditional_upper_235 {m : Nat} (p : Snake m) (hm : 1 ≤ m)
    (W : Nat)
    (hpacking : W + 2520 ≤ 5 *
      (24 * totalSingleton p + ∑ x, selected p x * shareN 12 p x))
    (hpotential : 4462 * (m-8) ≤ 9 * W + 5411) : m ≤ 235 := by
  have hb := charge_budget_with_loss p hm
  omega

theorem critical_case_exact_length {m : Nat} (p : Snake m) (hm : 235 ≤ m)
    (W : Nat)
    (hpacking : W + 2520 ≤ 5 *
      (24 * totalSingleton p + ∑ x, selected p x * shareN 12 p x))
    (hpotential : 4462 * (m-8) ≤ 9 * W + 5411) : m = 235 := by
  have hu := conditional_upper_235 p (by omega) W hpacking hpotential
  omega

#print axioms critical_loss_at_most_three
#print axioms critical_dominates
#print axioms conditional_upper_235
#print axioms critical_case_exact_length
end Snake9.Critical173
