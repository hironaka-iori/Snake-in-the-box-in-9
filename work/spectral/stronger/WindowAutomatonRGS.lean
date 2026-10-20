/-
Splitting the enumeration of restricted growth strings at a prefix length.

The kernel keeps every intermediate term of a `decide +kernel` proof until the declaration is
checked, so one enumeration of all 21,147 strings of length nine (L = 8) needs several
gigabytes.  `allRGS_of_prefixes` lets a table module check the continuations of each prefix in
its own declaration: if every RGS prefix of length `j` is listed and every listed prefix passes
the enumeration of its continuations, every RGS of length `j + n` passes.  Core Lean only.
-/
import WindowAutomatonCode

namespace Snake9.WindowAutomaton

/-- The growth bound after a prefix (the `m` that `isRGS` carries). -/
def rgsBound : List Nat → Nat → Nat
  | [], m => m
  | a :: l, m => rgsBound l (if m < a + 1 then a + 1 else m)

theorem isRGS_append_right : ∀ (l l' : List Nat) (m : Nat), isRGS (l ++ l') m = true → isRGS l' (rgsBound l m) = true
  | [], _, _, h => h
  | b :: l, l', m, h => by
    simp only [List.cons_append, isRGS, Bool.and_eq_true] at h
    exact isRGS_append_right l l' _ h.2

theorem allRGS_of_prefixes (p : List Nat → Bool) (j n : Nat) (pres : List (List Nat))
    (hok : pres.all (fun q => q.length == j && q.all (· < 8)) = true)
    (hcov : letN (maskOf shapeCode pres + 1) (fun M => allRGS j 0 (fun pre => Nat.testBit M (shapeCode pre))) = true)
    (h : ∀ pre, pre ∈ pres → allRGS n (rgsBound pre 0) (fun l => p (pre ++ l)) = true) (hj : j ≤ 8)
    (c : List Nat) (hc : c.length = j + n) (hr : isRGS c 0 = true) : p c = true := by
  have hsplit := List.take_append_drop j c
  have hr' : isRGS (c.take j ++ c.drop j) 0 = true := by rw [hsplit]; exact hr
  have hpreR := isRGS_append _ _ _ hr'
  have hlen : (c.take j).length = j := by simp [hc]
  rw [letN_succ] at hcov
  have hpre := allRGS_spec j 0 _ hcov (c.take j) hlen hpreR
  obtain ⟨q, hq, hqe⟩ := testBit_maskOf _ _ _ hpre
  have hq' : q.length = j ∧ ∀ a, a ∈ q → a < 8 := by
    have hall := hok
    simp only [List.all_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hall
    exact hall q hq
  have hqe' : q = c.take j := by
    unfold shapeCode at hqe
    exact codeFrom_inj q (c.take j) 1 (by rw [hq'.1, hlen]) hq'.2
      (fun a ha => by have := isRGS_bound _ _ hpreR a ha; omega) hqe
  have hrest := isRGS_append_right _ _ _ hr'
  rw [← hqe'] at hrest
  have := allRGS_spec n _ _ (h q hq) (c.drop j) (by simp [hc]; omega) hrest
  rw [hqe', hsplit] at this
  exact this

end Snake9.WindowAutomaton
