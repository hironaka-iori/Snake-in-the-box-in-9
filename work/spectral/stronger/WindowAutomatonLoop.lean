/-
Kernel-friendly loop and table primitives for the generated window-automaton checks.

The step tables are big natural numbers.  The kernel evaluates closed terms by
substitution, so a value shared by many loop iterations must be forced *once*
and re-entered as a literal: `letN (v + 1) k` reduces to `k v` with the kernel
first normalising `v + 1` to a numeral (the major premise of `Nat.rec`).  Every
inner-loop operation then runs on small numerals (`Nat.beq`, `Nat.ble`, `>>>`,
`&&&`), all of which the kernel computes natively.  Core Lean only.
-/
namespace Snake9.WindowAutomaton

/-- `allBelowR n p = p (n-1) && ... && p 0`, evaluated body-first so that the
kernel's recursion depth does not grow with `n`. -/
def allBelowR (n : Nat) (p : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun k ih => p k && ih) n

theorem allBelowR_succ (n : Nat) (p : Nat → Bool) : allBelowR (n + 1) p = (p n && allBelowR n p) := rfl

theorem allBelowR_spec : ∀ n (p : Nat → Bool), allBelowR n p = true → ∀ a, a < n → p a = true
  | 0, _, _, a, ha => absurd ha (Nat.not_lt_zero a)
  | n + 1, p, h, a, ha => by
    rw [allBelowR_succ, Bool.and_eq_true] at h
    by_cases hn : a = n
    · subst hn; exact h.1
    · exact allBelowR_spec n p h.2 a (by omega)

/-- `letN (v + 1) k = k v`; the kernel normalises `v + 1` to a numeral before
substituting, which turns `v` into a shared literal inside `k`. -/
def letN (n : Nat) (k : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (k 0) (fun m _ => k m) n

theorem letN_succ (n : Nat) (k : Nat → Bool) : letN (n + 1) k = k n := rfl

/-- Bit `c` of the table `T`. -/
def bitT (T c : Nat) : Bool := Nat.beq ((T >>> c) &&& 1) 1

/-- Window test: bit `c` of the forward table or of the reverse table. -/
def wtestT (T R c : Nat) : Bool := bitT T c || bitT R c

/-- `min R v` by a native comparison. -/
def clip (R v : Nat) : Nat := cond (Nat.ble v R) v R

theorem clip_le (R v : Nat) : clip R v ≤ R := by
  unfold clip
  cases h : Nat.ble v R
  · show R ≤ R; exact Nat.le_refl R
  · show v ≤ R; exact Nat.le_of_ble_eq_true h

/-- 4-bit field `c` of the table `P`, clipped to `R`. -/
def fldT (R P c : Nat) : Nat := clip R ((P >>> (4 * c)) &&& 15)

/-- Bits `a, ..., a + b - 1` of `T`, as a `b`-bit number. -/
def winT (T a b : Nat) : Nat := (T >>> a) &&& (2 ^ b - 1)

theorem bitT_eq_testBit (T c : Nat) : bitT T c = Nat.testBit T c := by
  unfold bitT
  rw [Nat.testBit_to_div_mod, Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow, Bool.eq_iff_iff,
    Nat.beq_eq, decide_eq_true_eq]

theorem bitT_win (T a b l : Nat) (hl : l < b) : bitT (winT T a b) l = bitT T (a + l) := by
  rw [bitT_eq_testBit, bitT_eq_testBit]
  unfold winT
  rw [Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one, decide_eq_true hl, Bool.and_true]

theorem wtestT_win (T R a b l : Nat) (hl : l < b) :
    wtestT (winT T a b) (winT R a b) l = wtestT T R (a + l) := by
  unfold wtestT
  rw [bitT_win _ _ _ _ hl, bitT_win _ _ _ _ hl]

theorem fldT_win (R P a b j : Nat) (hj : 4 * j + 4 ≤ b) :
    fldT R (winT P (4 * a) b) j = fldT R P (a + j) := by
  unfold fldT
  apply congrArg (clip R)
  apply Nat.eq_of_testBit_eq
  intro i
  unfold winT
  rw [Nat.testBit_and, Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_shiftRight, Nat.testBit_and,
    Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one]
  by_cases hi : i < 4
  · rw [decide_eq_true (by omega : 4 * j + i < b), Bool.and_true,
      show 4 * a + (4 * j + i) = 4 * (a + j) + i by omega]
  · have h15 : Nat.testBit 15 i = false := by
      rw [show (15 : Nat) = 2 ^ 4 - 1 by decide, Nat.testBit_two_pow_sub_one]
      exact decide_eq_false hi
    rw [h15, Bool.and_false, Bool.and_false]

end Snake9.WindowAutomaton
