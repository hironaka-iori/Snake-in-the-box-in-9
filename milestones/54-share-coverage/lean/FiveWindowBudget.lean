import CommonBudget
namespace Snake9.FiveWindowBudget

theorem window_budget (share demand : Nat → Nat) (J : Finset Nat) (N : Nat)
    (hJ : ∀ r ∈ J, r+5 < N)
    (hlocal : ∀ r ∈ J, demand r ≤ ∑ k ∈ Finset.range 5, share (r+k+1)) :
    (∑ r ∈ J, demand r) ≤ 5 * ∑ j ∈ Finset.range N, share j := by
  calc
    _ ≤ ∑ r ∈ J, ∑ k ∈ Finset.range 5, share (r+k+1) := Finset.sum_le_sum hlocal
    _ = ∑ k ∈ Finset.range 5, ∑ r ∈ J, share (r+k+1) := Finset.sum_comm
    _ ≤ ∑ k ∈ Finset.range 5, ∑ j ∈ Finset.range N, share j := by
      apply Finset.sum_le_sum
      intro k hk
      have hk5 : k < 5 := Finset.mem_range.mp hk
      have h := JointInterveningAccounting.shifted_sum_le share J N (k+1)
        (by intro r hr; have := hJ r hr; omega)
      simpa [Nat.add_assoc] using h
    _ = _ := by simp [Nat.mul_comm]

theorem aggregate_charge (B T S L G : Nat)
    (ht : B+14 ≤ T) (hl : L ≤ 5*S) (hg : G=24*T+S) :
    120*B+L+1680 ≤ 5*G := by omega

theorem current_model_bound (m G W : Nat)
    (hglobal : G+840*(m+1) ≤ 221136)
    (hbudget : W+1680 ≤ 5*G)
    (hpath : 3420*(m-7) ≤ 7*W+4380) :
    547*m ≤ 128782 := by omega

theorem current_model_integer_bound (m G W : Nat)
    (hglobal : G+840*(m+1) ≤ 221136)
    (hbudget : W+1680 ≤ 5*G)
    (hpath : 3420*(m-7) ≤ 7*W+4380) : m ≤ 235 := by
  have := current_model_bound m G W hglobal hbudget hpath
  omega

/-- A sufficient finite-model target; no path inequality of this strength is asserted. -/
theorem sufficient_for_234 (m G W R : Nat)
    (hglobal : G+840*(m+1) ≤ 221136)
    (hbudget : W+1680 ≤ 5*G)
    (hpath : 504*(m-7) ≤ W+R) (hr : R ≤ 2111) : m ≤ 234 := by omega

#print axioms window_budget
#print axioms aggregate_charge
#print axioms current_model_bound
#print axioms current_model_integer_bound
#print axioms sufficient_for_234
end Snake9.FiveWindowBudget
