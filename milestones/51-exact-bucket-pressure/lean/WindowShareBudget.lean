import JointChargeBudget
namespace Snake9.JointChargeBudget

theorem five_inside_seven (share : Nat → Nat) (r s : Nat) (hs : s≤2) :
    (∑ j ∈ Finset.range 5, share (r+s+j+1)) ≤
      ∑ j ∈ Finset.range 7, share (r+j+1) := by
  interval_cases s <;> simp [Finset.sum_range_succ, Nat.add_assoc] <;> omega

theorem joint_from_separate (D Q delta share : Nat)
    (hd : D≤delta) (hq : Q≤share) : 24*D+Q ≤ 24*delta+share := by omega

theorem five_bound_gives_joint (delta share : Nat → Nat) (r s D Q : Nat)
    (hs : s≤2) (hd : D ≤ ∑ j ∈ Finset.range 7, delta (r+j+1))
    (hq : Q ≤ ∑ j ∈ Finset.range 5, share (r+s+j+1)) :
    24*D+Q ≤ ∑ j ∈ Finset.range 7, localCharge delta share (r+j+1) := by
  have h := joint_from_separate D Q _ _ hd (hq.trans (five_inside_seven share r s hs))
  simpa [localCharge, Finset.sum_add_distrib, ← Finset.mul_sum] using h

#print axioms five_inside_seven
#print axioms joint_from_separate
#print axioms five_bound_gives_joint
end Snake9.JointChargeBudget
