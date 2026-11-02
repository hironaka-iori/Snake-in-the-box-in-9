import CountStateCode

namespace Snake9.Guards79
open Snake9.GraphInterpretation75

theorem encode_acc (xs : List Nat) (acc : Nat) :
    encodeCounts xs acc = acc * 6^xs.length + encodeCounts xs 0 := by
  induction xs generalizing acc with
  | nil => simp [encodeCounts]
  | cons a xs ih =>
    simp only [encodeCounts, List.length_cons, Nat.zero_mul, Nat.zero_add]
    rw [ih (acc*6+(a-1)), ih (a-1), pow_succ]
    ring

theorem encode_cons (a : Nat) (xs : List Nat) :
    encodeCounts (a::xs) 0 = (a-1)*6^xs.length + encodeCounts xs 0 := by
  simp only [encodeCounts, Nat.zero_mul, Nat.zero_add]
  exact encode_acc xs (a-1)

theorem encode_bound (xs : List Nat) (hx : ∀ x ∈ xs, 1 ≤ x ∧ x ≤ 6) :
    encodeCounts xs 0 < 6^xs.length := by
  induction xs with
  | nil => simp [encodeCounts]
  | cons a xs ih =>
    have ha := hx a List.mem_cons_self
    have ht := ih (fun x h => hx x (List.mem_cons_of_mem _ h))
    rw [encode_cons, List.length_cons, pow_succ]
    have hb : a-1 ≤ 5 := by omega
    have hm := Nat.mul_le_mul_right (6^xs.length) hb
    omega

theorem encoded_head (a : Nat) (xs : List Nat)
    (hx : ∀ x ∈ xs, 1 ≤ x ∧ x ≤ 6) :
    encodeCounts (a::xs) 0 / 6^xs.length = a-1 := by
  rw [encode_cons, Nat.add_comm, Nat.add_mul_div_right _ _ (by positivity),
    Nat.div_eq_of_lt (encode_bound xs hx), Nat.zero_add]

theorem encode_injective (xs ys : List Nat)
    (hx : ∀ x ∈ xs, 1 ≤ x ∧ x ≤ 6)
    (hy : ∀ y ∈ ys, 1 ≤ y ∧ y ≤ 6)
    (hlen : xs.length = ys.length)
    (heq : encodeCounts xs 0 = encodeCounts ys 0) : xs = ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all
  | cons a xs ih =>
    cases ys with
    | nil => simp at hlen
    | cons b ys =>
      have hl : xs.length = ys.length := by simpa using hlen
      have hxs : ∀ x ∈ xs, 1 ≤ x ∧ x ≤ 6 := fun x h => hx x (List.mem_cons_of_mem _ h)
      have hys : ∀ y ∈ ys, 1 ≤ y ∧ y ≤ 6 := fun y h => hy y (List.mem_cons_of_mem _ h)
      have hd := congrArg (fun v => v / 6^xs.length) heq
      dsimp only at hd
      rw [encoded_head a xs hxs, hl, encoded_head b ys hys] at hd
      have hab : a = b := by
        have ha := hx a List.mem_cons_self
        have hb := hy b List.mem_cons_self
        omega
      subst b
      rw [encode_cons, encode_cons, hl] at heq
      exact congrArg (List.cons a) (ih ys hxs hys hl (by omega))

#print axioms encode_acc
#print axioms encode_cons
#print axioms encode_bound
#print axioms encoded_head
#print axioms encode_injective
end Snake9.Guards79
