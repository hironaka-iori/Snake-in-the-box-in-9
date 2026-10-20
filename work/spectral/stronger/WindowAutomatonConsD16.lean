/-
The divide-and-conquer layout check `consD` of WindowAutomatonConsD for 16-bit fields:

  consD16_spec : consD16 n2 (n2 * m) (repK16 n2 m) d R C = true ->
      digit16 R (n3 * hb + l) = digit16 C (n2 * hb + l % n2)   for hb < 2 ^ d, l < n3.

Core Lean only.
-/
import WindowAutomatonSwar16

namespace Snake9.WindowAutomaton

def consD16 (n2 n3 rep d : Nat) : Nat → Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Bool)
    (fun R C => Nat.beq (winT R (16 * 0) (16 * n3)) (winT C (16 * 0) (16 * n2) * rep))
    (fun d rec R C =>
      rec (winT R (16 * 0) (16 * (n3 * 2 ^ d))) (winT C (16 * 0) (16 * (n2 * 2 ^ d))) &&
      rec (winT R (16 * (n3 * 2 ^ d)) (16 * (n3 * 2 ^ d))) (winT C (16 * (n2 * 2 ^ d)) (16 * (n2 * 2 ^ d))))
    d

theorem consD16_zero (n2 n3 rep R C : Nat) :
    consD16 n2 n3 rep 0 R C = Nat.beq (winT R (16 * 0) (16 * n3)) (winT C (16 * 0) (16 * n2) * rep) := rfl

theorem consD16_succ (n2 n3 rep d R C : Nat) :
    consD16 n2 n3 rep (d + 1) R C =
      (consD16 n2 n3 rep d (winT R (16 * 0) (16 * (n3 * 2 ^ d))) (winT C (16 * 0) (16 * (n2 * 2 ^ d))) &&
       consD16 n2 n3 rep d (winT R (16 * (n3 * 2 ^ d)) (16 * (n3 * 2 ^ d))) (winT C (16 * (n2 * 2 ^ d)) (16 * (n2 * 2 ^ d)))) :=
  rfl

theorem consD16_spec (n2 m : Nat) (hn2 : 0 < n2) :
    ∀ d R C, consD16 n2 (n2 * m) (repK16 n2 m) d R C = true →
      ∀ hb l, hb < 2 ^ d → l < n2 * m → digit16 R (n2 * m * hb + l) = digit16 C (n2 * hb + l % n2) := by
  intro d
  induction d with
  | zero =>
    intro R C h hb l hhb hl
    have hb0 : hb = 0 := by simp at hhb; omega
    subst hb0
    rw [consD16_zero] at h
    have h1 := Nat.eq_of_beq_eq_true h
    have h2 := congrArg (fun X => digit16 X l) h1
    simp only at h2
    rw [digit16_winT _ _ _ _ hl] at h2
    simp only [Nat.mul_zero, Nat.zero_add]
    rw [Nat.zero_add] at h2
    rw [h2]
    unfold winT
    rw [winT_pack16, ← pack16_tab_rep, digit16_pack _ (tab_bounded _ _ _ (fun _ _ => digit16_lt _ _)) l, tab_getD _ _ l hl,
      Nat.zero_add]
  | succ d ih =>
    intro R C h hb l hhb hl
    rw [consD16_succ, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    have hP : 2 ^ (d + 1) = 2 ^ d + 2 ^ d := by rw [Nat.pow_succ]; omega
    generalize hPd : 2 ^ d = P at h1 h2 hP ih
    have hn3 : 0 < n2 * m ∨ n2 * m = 0 := by omega
    have hlm : l % n2 < n2 := Nat.mod_lt _ hn2
    by_cases hlo : hb < P
    · have e := ih _ _ h1 hb l hlo hl
      have i1 : n2 * m * hb + l < n2 * m * P := by
        have : n2 * m * hb + n2 * m ≤ n2 * m * P := by
          rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hlo
        omega
      have i2 : n2 * hb + l % n2 < n2 * P := by
        have : n2 * hb + n2 ≤ n2 * P := by
          rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hlo
        omega
      rw [digit16_winT _ _ _ _ i1, digit16_winT _ _ _ _ i2, Nat.zero_add, Nat.zero_add] at e
      exact e
    · have hb' : hb - P < P := by omega
      have e := ih _ _ h2 (hb - P) l hb' hl
      have i1 : n2 * m * (hb - P) + l < n2 * m * P := by
        have : n2 * m * (hb - P) + n2 * m ≤ n2 * m * P := by
          rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hb'
        omega
      have i2 : n2 * (hb - P) + l % n2 < n2 * P := by
        have : n2 * (hb - P) + n2 ≤ n2 * P := by
          rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hb'
        omega
      rw [digit16_winT _ _ _ _ i1, digit16_winT _ _ _ _ i2] at e
      have hs : hb = P + (hb - P) := by omega
      have r1 : n2 * m * P + (n2 * m * (hb - P) + l) = n2 * m * hb + l := by
        conv => rhs; rw [hs, Nat.mul_add]
        omega
      have r2 : n2 * P + (n2 * (hb - P) + l % n2) = n2 * hb + l % n2 := by
        conv => rhs; rw [hs, Nat.mul_add]
        omega
      rw [r1, r2] at e
      exact e

end Snake9.WindowAutomaton
