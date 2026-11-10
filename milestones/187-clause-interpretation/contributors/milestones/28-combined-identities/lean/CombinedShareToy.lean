/-
Milestone 28, stage D: the arithmetic glue of a share-weighted k6 chain (toy, core Lean only).

The k6 automaton with step weight `120 * sym a(n+7) + S5 n` (S5 n = a certified lower bound on the
M = 12 share sum of the trailing 5-window, centres n+3 .. n+7) telescopes, exactly as
`invariant6`/`total_bound6`, to `P (m - 7) ≤ Q * Σ_{n < m-7} w n + R` (R = potential range).
This file proves, for arbitrary sequences, that this together with
  * the corner-share identity `Σ_{k ≤ m} (24 α k + share k) + 840 (m + 1) ≤ 221136`
    (`ShareBridge.core_charge_sum_le` with M = 12),
  * `4 ≤ α 0`, `4 ≤ α m`, `1 ≤ α j` inside, `sym ≤ α`,
  * the window lower bounds `S5 n ≤ share (n+3) + ... + share (n+7)` (`refuted_share_bridge`),
gives `(P + 4200 Q) m ≤ 1099800 Q + 7 P + R`.  With P/Q = 520 and R = 736 this is m ≤ 233.
Only the standard axioms are used (checked by `#print axioms` below).
-/
namespace Combined

def rsum (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => rsum f n + f n

theorem rsum_add (f g : Nat → Nat) (n : Nat) :
    rsum (fun k => f k + g k) n = rsum f n + rsum g n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [rsum, ih]; omega

theorem rsum_mul (c : Nat) (f : Nat → Nat) (n : Nat) :
    rsum (fun k => c * f k) n = c * rsum f n := by
  induction n with
  | zero => simp [rsum]
  | succ n ih => simp only [rsum, ih, Nat.mul_add]

theorem rsum_mono (f g : Nat → Nat) (n : Nat) (h : ∀ k, k < n → f k ≤ g k) :
    rsum f n ≤ rsum g n := by
  induction n with
  | zero => exact Nat.le_refl _
  | succ n ih =>
    simp only [rsum]
    have h1 := ih (fun k hk => h k (by omega))
    have h2 := h n (by omega)
    omega

theorem rsum_le_len (f : Nat → Nat) (n n' : Nat) (h : n ≤ n') : rsum f n ≤ rsum f n' := by
  induction n' with
  | zero => have : n = 0 := by omega
            subst this; exact Nat.le_refl _
  | succ n' ih =>
    by_cases hn : n = n' + 1
    · subst hn; exact Nat.le_refl _
    · have := ih (by omega); simp only [rsum]; omega

theorem rsum_shift (f : Nat → Nat) (s n : Nat) :
    rsum f s + rsum (fun k => f (k + s)) n = rsum f (n + s) := by
  induction n with
  | zero => simp [rsum]
  | succ n ih =>
    rw [show n + 1 + s = (n + s) + 1 by omega]
    simp only [rsum]
    omega

theorem shifted_le (f : Nat → Nat) (j N : Nat) (hj : j ≤ 8) :
    rsum (fun n => f (n + j)) N ≤ rsum f (N + 8) := by
  have h := rsum_shift f j N
  have h2 := rsum_le_len f (N + j) (N + 8) (by omega)
  omega

/-- Each 5-window `[n+3, n+7]`, `n < N`, is counted once: multiplicity at most 5. -/
theorem window5 (f : Nat → Nat) (N : Nat) :
    rsum (fun n => f (n+3) + f (n+4) + f (n+5) + f (n+6) + f (n+7)) N ≤ 5 * rsum f (N + 8) := by
  rw [rsum_add, rsum_add, rsum_add, rsum_add]
  have h3 := shifted_le f 3 N (by omega)
  have h4 := shifted_le f 4 N (by omega)
  have h5 := shifted_le f 5 N (by omega)
  have h6 := shifted_le f 6 N (by omega)
  have h7 := shifted_le f 7 N (by omega)
  omega

/-- The combined bound of a share-weighted k6 chain. -/
theorem combined_bound (P Q R m : Nat) (A sh sym S5 : Nat → Nat) (hm : 7 ≤ m)
    (htel : P * (m - 7) ≤ Q * rsum (fun n => 120 * sym (n + 7) + S5 n) (m - 7) + R)
    (hS5 : ∀ n, n < m - 7 → S5 n ≤ sh (n+3) + sh (n+4) + sh (n+5) + sh (n+6) + sh (n+7))
    (hsym : ∀ j, sym j ≤ A j)
    (hpos : ∀ j, 1 ≤ j → j + 1 ≤ m → 1 ≤ A j) (h0 : 4 ≤ A 0) (hmA : 4 ≤ A m)
    (hid : rsum (fun k => 24 * A k + sh k) (m + 1) + 840 * (m + 1) ≤ 221136) :
    (P + 4200 * Q) * m ≤ 1099800 * Q + 7 * P + R := by
  -- the window sum
  have hw : rsum S5 (m - 7) ≤ 5 * rsum sh (m + 1) := by
    have := rsum_mono S5 _ (m - 7) hS5
    have h2 := window5 sh (m - 7)
    rw [show m - 7 + 8 = m + 1 by omega] at h2
    omega
  -- the alpha part
  have ha : rsum (fun n => sym (n + 7)) (m - 7) ≤ rsum (fun n => A (n + 7)) (m - 7) :=
    rsum_mono _ _ _ (fun k _ => hsym (k + 7))
  have hsh := rsum_shift A 7 (m - 7)
  rw [show m - 7 + 7 = m by omega] at hsh
  have h7 : 10 ≤ rsum A 7 := by
    simp only [rsum]
    have := hpos 1 (by omega) (by omega); have := hpos 2 (by omega) (by omega)
    have := hpos 3 (by omega) (by omega); have := hpos 4 (by omega) (by omega)
    have := hpos 5 (by omega) (by omega); have := hpos 6 (by omega) (by omega)
    omega
  have hAm : rsum A (m + 1) = rsum A m + A m := rfl
  rw [rsum_add, rsum_mul] at hid
  -- the step-weight sum is at most 1099800 - 4200 m
  have hX : rsum (fun n => 120 * sym (n + 7) + S5 n) (m - 7) + 4200 * m ≤ 1099800 := by
    rw [rsum_add, rsum_mul]
    omega
  -- multiply by Q and combine with the telescoped potential inequality
  have hQ := Nat.mul_le_mul_left Q hX
  rw [Nat.mul_add] at hQ
  have hP : P * (m - 7) + P * 7 = P * m := by
    rw [← Nat.mul_add, show m - 7 + 7 = m by omega]
  have e1 : Q * (4200 * m) = 4200 * (Q * m) := Nat.mul_left_comm Q 4200 m
  have e2 : (P + 4200 * Q) * m = P * m + 4200 * (Q * m) := by
    rw [Nat.add_mul, Nat.mul_assoc]
  have e3 : Q * 1099800 = 1099800 * Q := Nat.mul_comm Q 1099800
  have e4 : P * 7 = 7 * P := Nat.mul_comm P 7
  rw [e1, e3] at hQ
  rw [e2]
  generalize Q * rsum (fun n => 120 * sym (n + 7) + S5 n) (m - 7) = X at hQ htel
  generalize P * (m - 7) = Y at htel hP
  generalize Q * m = qm at hQ ⊢
  generalize P * m = pm at hP ⊢
  omega

/-- The instance of the run: lambda = 520 (P = 520, Q = 1), potential range R = 736. -/
theorem m_le_233 (m : Nat) (h : (520 + 4200 * 1) * m ≤ 1099800 * 1 + 7 * 520 + 736) : m ≤ 233 := by
  omega

end Combined

#print axioms Combined.combined_bound
#print axioms Combined.m_le_233
