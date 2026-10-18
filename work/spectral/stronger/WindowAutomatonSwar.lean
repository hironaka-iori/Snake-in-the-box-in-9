/-
Word-parallel (SWAR) comparison of packed 8-bit fields, for the generated window-automaton checks.

A natural number is read as a list of base-256 digits, least significant first (`pack`).
If `A` and `B` pack digits `a_l <= 128` and `b_l < 128`, then `B + HI - A` (with `HI` the
pack of 128s) packs the digits `b_l + 128 - a_l`, without carries or borrows, and the top
bit of digit `l` is set exactly when `a_l <= b_l`.  One subtraction, one `&&&` and one `|||`
therefore test every field at once:

  swarOK A B BL HI = true  ->  for every l < n,  bit (8 l + 7) of BL  or  a_l <= b_l.

Core Lean only.
-/
import WindowAutomatonLoop

namespace Snake9.WindowAutomaton

-- `clip` comes from WindowAutomatonLoop

/-- `pack [d0, d1, ...] = d0 + 256 (d1 + 256 (...))`. -/
def pack : List Nat → Nat
  | [] => 0
  | d :: ds => d + 256 * pack ds

/-- Base-256 digit `j` of `n`. -/
def digit (n j : Nat) : Nat := n / 256 ^ j % 256

/-- The list `[f 0, f 1, ..., f (n-1)]`. -/
def tab (f : Nat → Nat) : Nat → List Nat
  | 0 => []
  | n + 1 => f 0 :: tab (fun j => f (j + 1)) n

/-- All entries below `b`. -/
def Bounded (b : Nat) : List Nat → Prop
  | [] => True
  | d :: ds => d < b ∧ Bounded b ds

theorem tab_length (f : Nat → Nat) (n : Nat) : (tab f n).length = n := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih => simp [tab, ih]

theorem tab_getD (f : Nat → Nat) (n : Nat) : ∀ j, j < n → (tab f n).getD j 0 = f j := by
  induction n generalizing f with
  | zero => intro j hj; omega
  | succ n ih =>
    intro j hj
    cases j with
    | zero => rfl
    | succ j => simp only [tab, List.getD_cons_succ]; exact ih _ j (by omega)

theorem tab_bounded (f : Nat → Nat) (b n : Nat) (h : ∀ j, j < n → f j < b) : Bounded b (tab f n) := by
  induction n generalizing f with
  | zero => trivial
  | succ n ih => exact ⟨h 0 (by omega), ih _ (fun j hj => h (j + 1) (by omega))⟩

theorem digit_pack (ds : List Nat) (h : Bounded 256 ds) : ∀ j, digit (pack ds) j = ds.getD j 0 := by
  induction ds with
  | nil => intro j; simp [pack, digit]
  | cons d ds ih =>
    intro j
    cases j with
    | zero =>
      simp only [digit, pack, Nat.pow_zero, Nat.div_one, List.getD_cons_zero]
      have := h.1
      omega
    | succ j =>
      have e : digit (pack (d :: ds)) (j + 1) = digit (pack ds) j := by
        unfold digit
        simp only [pack, Nat.pow_succ]
        rw [show 256 ^ j * 256 = 256 * 256 ^ j by omega, ← Nat.div_div_eq_div_mul]
        have h1 : (d + 256 * pack ds) / 256 = pack ds := by
          have := h.1
          omega
        rw [h1]
      rw [e, ih h.2 j]
      rfl

/-- Digit-wise addition. -/
def zipAdd : List Nat → List Nat → List Nat
  | d :: ds, e :: es => (d + e) :: zipAdd ds es
  | ds, [] => ds
  | [], es => es

theorem pack_zipAdd (ds es : List Nat) : pack (zipAdd ds es) = pack ds + pack es := by
  induction ds generalizing es with
  | nil => cases es <;> simp [zipAdd, pack]
  | cons d ds ih =>
    cases es with
    | nil => simp [zipAdd, pack]
    | cons e es =>
      simp only [zipAdd, pack, ih]
      omega

theorem zipAdd_tab (f g : Nat → Nat) (n : Nat) : zipAdd (tab f n) (tab g n) = tab (fun j => f j + g j) n := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih => simp [tab, zipAdd, ih]

theorem pack_tab_add (f g : Nat → Nat) (n : Nat) :
    pack (tab f n) + pack (tab g n) = pack (tab (fun j => f j + g j) n) := by
  rw [← pack_zipAdd, zipAdd_tab]

/-- Digit-wise subtraction (`g j <= f j`). -/
theorem pack_tab_sub (f g : Nat → Nat) (n : Nat) (h : ∀ j, j < n → g j ≤ f j) :
    pack (tab f n) - pack (tab g n) = pack (tab (fun j => f j - g j) n) := by
  have e := pack_tab_add (fun j => f j - g j) g n
  have e2 : tab (fun j => f j - g j + g j) n = tab f n := by
    clear e
    induction n generalizing f g with
    | zero => rfl
    | succ n ih =>
      simp only [tab]
      rw [Nat.sub_add_cancel (h 0 (by omega))]
      congr 1
      exact ih _ _ (fun j hj => h (j + 1) (by omega))
  rw [e2] at e
  omega

theorem digit_div (x j : Nat) : digit (x / 256) j = digit x (j + 1) := by
  unfold digit
  rw [Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm]

/-- Every number is the pack of its digits, modulo `256 ^ n`. -/
theorem pack_tab_digit_mod (n : Nat) : ∀ x, pack (tab (digit x) n) = x % 256 ^ n := by
  induction n with
  | zero => intro x; simp [tab, pack, Nat.mod_one]
  | succ n ih =>
    intro x
    simp only [tab, pack]
    have h1 : (fun j => digit x (j + 1)) = digit (x / 256) := by
      funext j; exact (digit_div x j).symm
    rw [h1, ih, Nat.pow_succ, Nat.mul_comm (256 ^ n) 256, Nat.mod_mul]
    simp [digit]

theorem pack_tab_digit (x n : Nat) (hx : x < 256 ^ n) : pack (tab (digit x) n) = x := by
  rw [pack_tab_digit_mod, Nat.mod_eq_of_lt hx]

theorem pack_lt (ds : List Nat) (h : Bounded 256 ds) : pack ds < 256 ^ ds.length := by
  induction ds with
  | nil => simp [pack]
  | cons d ds ih =>
    simp only [pack, List.length_cons, Nat.pow_succ]
    have := ih h.2
    have := h.1
    omega

/-- Bit `8 l + 7` of `n` is the top bit of digit `l`. -/
theorem testBit_digit (n l : Nat) : Nat.testBit n (8 * l + 7) = Nat.testBit (digit n l) 7 := by
  unfold digit
  rw [show 256 ^ l = 2 ^ (8 * l) by simp [Nat.pow_mul], ← Nat.shiftRight_eq_div_pow,
    show (256 : Nat) = 2 ^ 8 by rfl, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
  try simp

theorem testBit_top (d : Nat) (hd : d < 256) : Nat.testBit d 7 = decide (128 ≤ d) := by
  rw [Nat.testBit_to_div_mod, Bool.eq_iff_iff, decide_eq_true_eq, decide_eq_true_eq]
  simp only [Nat.reducePow]
  omega

/-- The field-wise test. -/
def swarOK (A B BL HI : Nat) : Bool := Nat.beq ((((B + HI) - A) &&& HI) ||| BL) HI

theorem swarOK_spec (n : Nat) (a b : Nat → Nat) (A B BL : Nat)
    (hA : A = pack (tab a n)) (hB : B = pack (tab b n))
    (ha : ∀ l, l < n → a l ≤ 128) (hb : ∀ l, l < n → b l < 128)
    (h : swarOK A B BL (pack (tab (fun _ => 128) n)) = true) (l : Nat) (hl : l < n) :
    Nat.testBit BL (8 * l + 7) = true ∨ a l ≤ b l := by
  unfold swarOK at h
  have heq := Nat.eq_of_beq_eq_true h
  subst hA hB
  rw [pack_tab_add, pack_tab_sub _ _ _ (fun j hj => by have := ha j hj; omega)] at heq
  -- bit 8 l + 7 of both sides
  have hbit := congrArg (fun x => Nat.testBit x (8 * l + 7)) heq
  simp only [Nat.testBit_or, Nat.testBit_and] at hbit
  have hhi : Nat.testBit (pack (tab (fun _ => 128) n)) (8 * l + 7) = true := by
    rw [testBit_digit, digit_pack _ (tab_bounded _ _ _ (fun _ _ => by decide)) l, tab_getD _ _ l hl]
    decide
  have hz : Nat.testBit (pack (tab (fun j => b j + 128 - a j) n)) (8 * l + 7) = decide (a l ≤ b l) := by
    rw [testBit_digit, digit_pack _ (tab_bounded _ _ _ (fun j hj => by have := hb j hj; omega)) l,
      tab_getD _ _ l hl, testBit_top _ (by have := hb l hl; omega)]
    rw [Bool.eq_iff_iff, decide_eq_true_eq, decide_eq_true_eq]
    have := ha l hl
    omega
  rw [hhi, hz, Bool.and_true] at hbit
  cases hd : decide (a l ≤ b l) with
  | true => exact Or.inr (of_decide_eq_true hd)
  | false =>
    rw [hd, Bool.false_or] at hbit
    exact Or.inl hbit

/-- A window of `n` 8-bit fields starting at field `a` of a table. -/
theorem winT_pack (T a n : Nat) :
    (T >>> (8 * a)) &&& (2 ^ (8 * n) - 1) = pack (tab (fun l => digit T (a + l)) n) := by
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]
  have e8 : ∀ m, (2 : Nat) ^ (8 * m) = 256 ^ m := fun m => by simp [Nat.pow_mul]
  have h : (fun l => digit T (a + l)) = digit (T / 2 ^ (8 * a)) := by
    funext l
    unfold digit
    rw [Nat.div_div_eq_div_mul, e8, ← Nat.pow_add]
  rw [h, pack_tab_digit_mod, e8 n]

theorem pack_tab_mul (c : Nat) (f : Nat → Nat) (n : Nat) : c * pack (tab f n) = pack (tab (fun j => c * f j) n) := by
  induction n generalizing f with
  | zero => simp [tab, pack]
  | succ n ih =>
    simp only [tab, pack]
    rw [Nat.mul_add, ← Nat.mul_assoc, Nat.mul_comm c 256, Nat.mul_assoc, ih]

/-- Bit `l` of the window of `b` bits of `T` starting at `a`. -/
theorem testBit_win (T a b l : Nat) (hl : l < b) : Nat.testBit ((T >>> a) &&& (2 ^ b - 1)) l = Nat.testBit T (a + l) := by
  rw [Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one, decide_eq_true hl, Bool.and_true]

/-- Forward and reverse tables of one window, merged. -/
def blk (S R : Nat) : Nat := S ||| R

theorem testBit_blk (S R i : Nat) : Nat.testBit (blk S R) i = (Nat.testBit S i || Nat.testBit R i) := by
  unfold blk; exact Nat.testBit_or S R i

theorem testBit_blk_win (S R a b l : Nat) (hl : l < b) :
    Nat.testBit (blk ((S >>> a) &&& (2 ^ b - 1)) ((R >>> a) &&& (2 ^ b - 1))) l = Nat.testBit (blk S R) (a + l) := by
  rw [testBit_blk, testBit_blk, testBit_win _ _ _ _ hl, testBit_win _ _ _ _ hl]

/-- Six fields `f 0 .. f 5`, each repeated six times: `stretch6 F * rep6 = pack [f0,f0,...,f5]`. -/
def stretch6 (F : Nat) : Nat :=
  digit F 0 + digit F 1 * 2 ^ 48 + digit F 2 * 2 ^ 96 + digit F 3 * 2 ^ 144 + digit F 4 * 2 ^ 192 + digit F 5 * 2 ^ 240

def rep6 : Nat := 1 + 2 ^ 8 + 2 ^ 16 + 2 ^ 24 + 2 ^ 32 + 2 ^ 40

theorem stretch6_rep6 (F : Nat) : stretch6 F * rep6 = pack (tab (fun l => digit F (l / 6)) 36) := by
  simp only [stretch6, rep6, tab, pack, Nat.reduceAdd, Nat.reduceDiv, Nat.reducePow]
  omega

theorem tab_congr (f g : Nat → Nat) (n : Nat) (h : ∀ j, j < n → f j = g j) : tab f n = tab g n := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih => simp only [tab]; rw [h 0 (by omega), ih _ _ (fun j hj => h (j + 1) (by omega))]

theorem pack_tab_append (f : Nat → Nat) (n m : Nat) :
    pack (tab f (n + m)) = pack (tab f n) + 256 ^ n * pack (tab (fun j => f (n + j)) m) := by
  induction n generalizing f with
  | zero => simp [tab, pack]
  | succ n ih =>
    rw [Nat.succ_add]
    simp only [tab, pack]
    rw [ih (fun j => f (j + 1))]
    simp only [Nat.pow_succ]
    have : (fun j => f (n + j + 1)) = fun j => f (n + 1 + j) := by funext j; congr 1; omega
    rw [this, Nat.mul_comm (256 ^ n) 256, Nat.mul_assoc]
    omega

/-- `[f 0, ..., f (n-1)]` repeated `m` times is the pack times `1 + 256^n + ... + 256^(n (m-1))`. -/
def repK (n : Nat) : Nat → Nat
  | 0 => 0
  | m + 1 => repK n m + 256 ^ (n * m)

theorem pack_tab_rep (f : Nat → Nat) (n : Nat) : ∀ m, pack (tab (fun l => f (l % n)) (n * m)) = pack (tab f n) * repK n m
  | 0 => by simp [tab, pack, repK]
  | m + 1 => by
    rw [Nat.mul_succ, pack_tab_append, pack_tab_rep f n m]
    have h2 : tab (fun j => f ((n * m + j) % n)) n = tab f n := by
      apply tab_congr; intro j hj
      rw [show n * m + j = j + n * m by omega, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]
    rw [h2, repK, Nat.mul_add, Nat.mul_comm (pack (tab f n)) (256 ^ (n * m))]

theorem clip_eq_of_le (R v : Nat) (h : v ≤ R) : clip R v = v := by
  unfold clip; rw [Nat.ble_eq_true_of_le h]; rfl

theorem digit_lt (n j : Nat) : digit n j < 256 := Nat.mod_lt _ (by decide)

end Snake9.WindowAutomaton
