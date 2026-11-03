import SumBudget112

/-! Add a two-position deficit to the existing shared window budget.
The local pair lower bound remains a hypothesis. No new definitions. -/
namespace Snake9.PairBudget113
open Finset
open scoped BigOperators

theorem pair_deficit_le (x y lower : Nat) (h : lower ≤ x+y) :
    lower-(min 6 x+min 6 y) ≤ (x-min 6 x)+(y-min 6 y) := by
  have hx := Nat.min_le_right 6 x
  have hy := Nat.min_le_right 6 y
  omega

theorem shared_pair_budget (delta credit pair : Nat → Nat) (m a b : Nat)
    (hcapacity : 4*a+b ≤ 120)
    (hcredit : ∀ r < m-8, credit r ≤
      a*(delta (r+4)+delta (r+5)+delta (r+7)+delta (r+8))+b*delta (r+6))
    (hpair : ∀ r < m-8, pair r ≤ delta (r+4)+delta (r+8)) :
    (∑ r ∈ Finset.range (m-8), max (credit r) (a*pair r)) ≤
      120 * ∑ i ∈ Finset.range (m+1), delta i := by
  apply SumBudget112.weighted_window_budget delta _ m a b hcapacity
  intro r hr
  apply max_le (hcredit r hr)
  have hp := Nat.mul_le_mul_left a (hpair r hr)
  nlinarith

theorem shared_count_pair_budget (alpha credit lower : Nat → Nat) (m a b : Nat)
    (hcapacity : 4*a+b ≤ 120)
    (hcredit : ∀ r < m-8, credit r ≤
      a*((alpha (r+4)-min 6 (alpha (r+4)))+
        (alpha (r+5)-min 6 (alpha (r+5)))+
        (alpha (r+7)-min 6 (alpha (r+7)))+
        (alpha (r+8)-min 6 (alpha (r+8))))+
      b*(alpha (r+6)-min 6 (alpha (r+6))))
    (hpair : ∀ r < m-8, lower r ≤ alpha (r+4)+alpha (r+8)) :
    (∑ r ∈ Finset.range (m-8), max (credit r)
      (a*(lower r-(min 6 (alpha (r+4))+min 6 (alpha (r+8)))))) ≤
      120 * ∑ i ∈ Finset.range (m+1), (alpha i-min 6 (alpha i)) := by
  apply shared_pair_budget (fun i => alpha i-min 6 (alpha i)) _ _ m a b
    hcapacity hcredit
  intro r hr
  exact pair_deficit_le _ _ _ (hpair r hr)

#print axioms pair_deficit_le
#print axioms shared_pair_budget
#print axioms shared_count_pair_budget
end Snake9.PairBudget113
