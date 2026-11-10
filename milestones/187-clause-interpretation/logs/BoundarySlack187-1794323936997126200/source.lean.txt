import Combined187
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Combined187

theorem rsum_const (q n : Nat) : rsum (fun _ => q) n = q*n := by
  induction n with
  | zero => simp [rsum]
  | succ n ih => simp only [rsum,ih,Nat.mul_succ]

theorem boundary_twenty_two (A : Nat → Nat) (m : Nat)
    (h0 : 4 ≤ A 0) (hm : 4 ≤ A m)
    (h6 : 14 ≤ A 1 + A 2 + A 3 + A 4 + A 5 + A 6) :
    22 ≤ rsum A 7 + A m := by
  simp only [rsum]
  omega

theorem budget_with_share_slack (m q L : Nat) (A sh sym S5 : Nat → Nat)
    (hm : 7 ≤ m)
    (hS5 : ∀ n, n < m-7 → S5 n ≤ sh (n+3)+sh (n+4)+sh (n+5)+sh (n+6)+sh (n+7)+q)
    (hsym : ∀ j, sym j ≤ A j)
    (hb : 22 ≤ rsum A 7 + A m)
    (hid : rsum (fun k => 24*A k+sh k) (m+1)+840*(m+1)+L ≤ 221136) :
    rsum (fun n => 120*sym (n+7)+S5 n) (m-7)+4200*m+5*L ≤ 1098840+q*(m-7) := by
  have hw : rsum S5 (m-7) ≤ 5*rsum sh (m+1)+q*(m-7) := by
    have h := rsum_mono S5 _ (m-7) hS5
    rw [rsum_add,rsum_const] at h
    have h2 := window5 sh (m-7)
    rw [show m-7+8=m+1 by omega] at h2
    omega
  have ha : rsum (fun n => sym (n+7)) (m-7) ≤ rsum (fun n => A (n+7)) (m-7) :=
    rsum_mono _ _ _ (fun k _ => hsym (k+7))
  have hs := rsum_shift A 7 (m-7)
  rw [show m-7+7=m by omega] at hs
  have he : rsum A (m+1)=rsum A m+A m := rfl
  rw [rsum_add,rsum_mul] at hid
  rw [rsum_add,rsum_mul]
  omega

theorem four_point_slack (m W L : Nat) (hm : 7 ≤ m)
    (hb : W+4200*m+5*L ≤ 1098840+4*(m-7))
    (ht : 520*(m-7) ≤ W+1023) :
    4716*m+5*L ≤ 1103475 ∧ m ≤ 233 := by omega

theorem five_point_slack (m W L : Nat) (hm : 7 ≤ m)
    (hb : W+4200*m+5*L ≤ 1098840+5*(m-7))
    (ht : 520*(m-7) ≤ W+784) :
    4715*m+5*L ≤ 1103229 ∧ m ≤ 233 := by omega

theorem encoded_range_five_point_obstruction :
    520*(234-7) ≤ 117017+1023 ∧
    117017+4200*234 ≤ 1098840+5*(234-7) := by decide +kernel

theorem exact_range_six_point_obstruction :
    520*(234-7) ≤ 117256+784 ∧
    117256+4200*234 ≤ 1098840+6*(234-7) := by decide +kernel

#print axioms rsum_const
#print axioms boundary_twenty_two
#print axioms budget_with_share_slack
#print axioms four_point_slack
#print axioms five_point_slack
#print axioms encoded_range_five_point_obstruction
#print axioms exact_range_six_point_obstruction
end Combined187
