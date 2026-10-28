import FiveWindowBudget
namespace Snake9.ExtendedBudget59

theorem window_budget (share demand : Nat → Nat) (J : Finset Nat) (N offset : Nat)
    (hJ : ∀ r ∈ J, r+offset+4 < N)
    (hlocal : ∀ r ∈ J, demand r ≤ ∑ k ∈ Finset.range 5, share (r+k+offset)) :
    (∑ r ∈ J, demand r) ≤ 5 * ∑ j ∈ Finset.range N, share j := by
  calc
    _ ≤ ∑ r ∈ J, ∑ k ∈ Finset.range 5, share (r+k+offset) := Finset.sum_le_sum hlocal
    _ = ∑ k ∈ Finset.range 5, ∑ r ∈ J, share (r+k+offset) := Finset.sum_comm
    _ ≤ ∑ k ∈ Finset.range 5, ∑ j ∈ Finset.range N, share j := by
      apply Finset.sum_le_sum
      intro k hk
      have hk5 : k < 5 := Finset.mem_range.mp hk
      have h := JointInterveningAccounting.shifted_sum_le share J N (k+offset)
        (by intro r hr; have := hJ r hr; omega)
      simpa [Nat.add_assoc] using h
    _ = _ := by simp [Nat.mul_comm]

theorem aggregate_charge (B T S L G : Nat)
    (ht : B+15 ≤ T) (hl : L ≤ 5*S) (hg : G=24*T+S) :
    120*B+L+1800 ≤ 5*G := by omega

theorem global_charge (m G W : Nat)
    (hg : G+840*(m+1) ≤ 221136) (hw : W+1800 ≤ 5*G) :
    W+4200*m ≤ 1099680 := by omega

theorem potential_bound (m p d W R : Int) (hd : 0≤d)
    (hb : W+4200*m ≤ 1099680) (hp : p*(m-8)≤d*W+R) :
    (p+4200*d)*m ≤ 1099680*d+8*p+R := by
  have := mul_le_mul_of_nonneg_left hb hd
  nlinarith

theorem extended_model_bound (m G W : Nat)
    (hg : G+840*(m+1) ≤ 221136) (hw : W+1800 ≤ 5*G)
    (hp : 9891*(m-8) ≤ 20*W+12101) : m ≤ 235 := by omega

theorem mean_insufficient_for_234 (mu rho : ℚ)
    (hm : mu ≤ 9891/20) (hr : 0 ≤ rho) :
    235*(4200+mu) ≤ 1099680+8*mu+rho := by linarith

#print axioms window_budget
#print axioms aggregate_charge
#print axioms global_charge
#print axioms potential_bound
#print axioms extended_model_bound
#print axioms mean_insufficient_for_234
end Snake9.ExtendedBudget59
