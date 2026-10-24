import JointExcess

namespace SixCountStateBudget

theorem seven_window_budget (delta demand : Nat → Nat) (J : Finset Nat) (N : Nat)
    (hJ : ∀ r ∈ J, r+7 < N)
    (hlocal : ∀ r ∈ J, demand r ≤ ∑ k ∈ Finset.range 7, delta (r+k+1)) :
    (∑ r ∈ J, demand r) ≤ 7 * ∑ j ∈ Finset.range N, delta j := by
  calc
    _ ≤ ∑ r ∈ J, ∑ k ∈ Finset.range 7, delta (r+k+1) := Finset.sum_le_sum hlocal
    _ = ∑ k ∈ Finset.range 7, ∑ r ∈ J, delta (r+k+1) := Finset.sum_comm
    _ ≤ ∑ k ∈ Finset.range 7, ∑ j ∈ Finset.range N, delta j := by
      apply Finset.sum_le_sum
      intro k hk
      have hk7 : k < 7 := Finset.mem_range.mp hk
      have h := JointInterveningAccounting.shifted_sum_le delta J N (k+1)
        (by intro r hr; have := hJ r hr; omega)
      simpa [Nat.add_assoc] using h
    _ = _ := by simp [Nat.mul_comm]

theorem combined_charge (B D Q share C G : Nat)
    (hq : Q ≤ 7*D) (hs : 6*C ≤ share)
    (hg : G = 24*(B+D)+share) : 168*B+24*Q+42*C ≤ 7*G := by omega

theorem maximum_demand (a b W : Nat) (ha : a ≤ W) (hb : b ≤ W) : max a b ≤ W :=
  max_le ha hb

#print axioms seven_window_budget
#print axioms combined_charge
#print axioms maximum_demand
end SixCountStateBudget
