import AttachmentBalance191

namespace CollisionRepair200
open Replacement191

theorem oneCover : ∀ a b c d : Bool, c && d = false →
    (if a && b then 1 else 0 : Nat) ≤
      (if a && !c then 1 else 0) + (if b && !d then 1 else 0) := by
  decide +kernel

theorem collisionCovered {V : Type} (xs : List V) (p q r s : V → Bool)
    (disjoint : ∀ v ∈ xs, r v && s v = false) :
    count xs (fun v => p v && q v) ≤
      count xs (fun v => p v && !r v) + count xs (fun v => q v && !s v) := by
  induction xs with
  | nil => simp [count]
  | cons v vs ih =>
    have hv := oneCover (p v) (q v) (r v) (s v) (disjoint v (by simp))
    have ht := ih (fun w hw => disjoint w (by simp [hw]))
    simp only [count]
    omega

theorem repairBalance {V : Type} (xs : List V) (p q r s : V → Bool)
    (oldSize : count xs p + count xs q = 102)
    (newSize : count xs r + count xs s = 100) :
    count xs (fun v => p v && !r v) + count xs (fun v => q v && !s v) =
      count xs (fun v => r v && !p v) + count xs (fun v => s v && !q v) + 2 := by
  have hp := countPartition xs p r
  have hq := countPartition xs q s
  have hr := countPartition xs r p
  have hs := countPartition xs s q
  have hpr := intersectionSymmetric xs p r
  have hqs := intersectionSymmetric xs q s
  omega

theorem trimmingCutoff (retained deleted collisions : Nat)
    (size : retained + deleted = 102) (cover : collisions ≤ deleted)
    (competitive : 92 ≤ retained) : deleted ≤ 10 ∧ collisions ≤ 10 := by
  omega

theorem contactCase0 (a b c d : Nat)
    (ha : a ≤ b) (hb : b ≤ 51) (hc : c ≤ d) (hd : d ≤ 51)
    (first : ¬ (a ≤ 38 ∧ 38 < b ∧ c ≤ 43 ∧ 43 < d))
    (second : ¬ (a ≤ 43 ∧ 43 < b ∧ c ≤ 38 ∧ 38 < d)) :
    (b-a)+(d-c) ≤ 89 := by omega

theorem contactCase1 (a b c d : Nat)
    (ha : a ≤ b) (hb : b ≤ 51) (hc : c ≤ d) (hd : d ≤ 51)
    (first : ¬ (a ≤ 4 ∧ 4 < b ∧ c ≤ 38 ∧ 38 < d))
    (second : ¬ (a ≤ 38 ∧ 38 < b ∧ c ≤ 4 ∧ 4 < d)) :
    (b-a)+(d-c) ≤ 92 := by omega

#print axioms oneCover
#print axioms collisionCovered
#print axioms repairBalance
#print axioms trimmingCutoff
#print axioms contactCase0
#print axioms contactCase1
end CollisionRepair200
