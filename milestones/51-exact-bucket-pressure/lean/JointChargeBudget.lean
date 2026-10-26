import CommonBudget
import Mathlib.Tactic
namespace Snake9.JointChargeBudget

def localCharge (delta share : Nat → Nat) (i : Nat) : Nat := 24*delta i+share i

theorem joint_window_budget (delta share demand : Nat → Nat) (J : Finset Nat) (N : Nat)
    (hJ : ∀ r ∈ J, r+7 < N)
    (hlocal : ∀ r ∈ J, demand r ≤ ∑ k ∈ Finset.range 7, localCharge delta share (r+k+1)) :
    (∑ r ∈ J, demand r) ≤ 7*(24*(∑ j ∈ Finset.range N, delta j)+(∑ j ∈ Finset.range N, share j)) := by
  have h := SixCountStateBudget.seven_window_budget (localCharge delta share) demand J N hJ hlocal
  simpa [localCharge, Finset.sum_add_distrib, ← Finset.mul_sum] using h

theorem maximum_joint_bound (a b windowCharge : Nat)
    (ha : a ≤ windowCharge) (hb : b ≤ windowCharge) : max a b ≤ windowCharge := max_le ha hb

theorem joint_only_charge (B D S R G : Nat)
    (hr : R ≤ 7*(24*D+S)) (hg : G=24*(B+D)+S) : 168*B+R ≤ 7*G := by omega

/-- A sum of separately budgeted arguments; a local share is never added twice to one budget. -/
theorem mixed_charge (B D S Q C R G : Nat)
    (hq : Q ≤ 7*D) (hc : 6*C ≤ S) (hr : R ≤ 7*(24*D+S))
    (hg : G=24*(B+D)+S) : 336*B+24*Q+42*C+R ≤ 14*G := by omega

theorem mixed_target_235 (m G W R : Nat)
    (hglobal : G+840*(m+1) ≤ 221136)
    (hbudget : W+4704 ≤ 14*G)
    (hpath : 1344*(m-7) ≤ W+R) (hr : R ≤ 3695) : m ≤ 235 := by omega

#print axioms joint_window_budget
#print axioms maximum_joint_bound
#print axioms joint_only_charge
#print axioms mixed_charge
#print axioms mixed_target_235
end Snake9.JointChargeBudget
