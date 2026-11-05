import Std

namespace Snake9.SmallLossArithmetic174

theorem positive_count_le_sum (l : List Nat) :
    l.countP (fun n => 0 < n) ≤ l.sum := by
  induction l with
  | nil => simp
  | cons n l ih =>
    simp only [List.countP_cons,List.sum_cons]
    by_cases hn : 0 < n
    · simp only [hn,decide_true,Bool.true_eq,ite_true]
      omega
    · simp only [hn,decide_false,Bool.false_eq_true,ite_false]
      omega

theorem small_loss_support (l : List Nat) (h : l.sum ≤ 3) :
    l.countP (fun n => 0 < n) ≤ 3 := by
  have hc := positive_count_le_sum l
  omega

theorem degree_five_excludes_residue_two (e L : Nat)
    (h : (12*e)%5 ≤ L) (hl : L ≤ 3) : e%5 ≠ 2 := by
  intro he
  have hr : (12*e)%5 = 4 := by rw [Nat.mul_mod,he]
  omega

theorem zero_loss_divisibility (d e : Nat) (h : (12*e)%d = 0) : d ∣ 12*e :=
  Nat.dvd_of_mod_eq_zero h

#print axioms positive_count_le_sum
#print axioms small_loss_support
#print axioms degree_five_excludes_residue_two
#print axioms zero_loss_divisibility
end Snake9.SmallLossArithmetic174
