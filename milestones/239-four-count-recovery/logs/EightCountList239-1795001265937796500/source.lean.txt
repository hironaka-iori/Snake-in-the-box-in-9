import Std

set_option Elab.async false
set_option maxRecDepth 12000
set_option maxHeartbeats 1000000

namespace EightCountDominance239

theorem list_sum_bounds (B : Int) (xs : List Int)
    (hxs : ∀ x ∈ xs, -B ≤ x ∧ x ≤ B) :
    -((xs.length : Int) * B) ≤ xs.sum ∧
      xs.sum ≤ (xs.length : Int) * B := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    have ha := hxs a List.mem_cons_self
    have ht := ih (fun x hx => hxs x (List.mem_cons_of_mem a hx))
    simp only [List.sum_cons, List.length_cons, Int.natCast_succ,
      Int.add_mul, Int.one_mul]
    constructor
    · calc
        -((xs.length : Int) * B + B) = -B + -((xs.length : Int) * B) := by
          rw [Int.neg_add, Int.add_comm]
        _ ≤ a + xs.sum := Int.add_le_add ha.1 ht.1
    · calc
        a + xs.sum ≤ B + (xs.length : Int) * B := Int.add_le_add ha.2 ht.2
        _ = (xs.length : Int) * B + B := Int.add_comm _ _

#print axioms list_sum_bounds

end EightCountDominance239
