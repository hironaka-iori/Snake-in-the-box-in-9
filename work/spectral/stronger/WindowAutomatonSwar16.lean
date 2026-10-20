/-
16-bit-field version of the SWAR comparison of WindowAutomatonSwar (same statements with base
65536 instead of 256: `pack16`, `digit16`, `repK16`, `swarOK16_spec`, ...).  Potentials of range up
to 32767 fit; `swarOK` itself is shared (it never mentions the field width), so are `tab`,
`Bounded`, `zipAdd`, `blk` and the window lemmas.  Core Lean only.
-/
import WindowAutomatonSwar

namespace Snake9.WindowAutomaton

/-- `pack16 [d0, d1, ...] = d0 + 65536 (d1 + 65536 (...))`. -/
def pack16 : List Nat → Nat
  | [] => 0
  | d :: ds => d + 65536 * pack16 ds

/-- Base-65536 digit `j` of `n`. -/
def digit16 (n j : Nat) : Nat := n / 65536 ^ j % 65536

theorem digit16_pack (ds : List Nat) (h : Bounded 65536 ds) : ∀ j, digit16 (pack16 ds) j = ds.getD j 0 := by
  induction ds with
  | nil => intro j; simp [pack16, digit16]
  | cons d ds ih =>
    intro j
    cases j with
    | zero =>
      simp only [digit16, pack16, Nat.pow_zero, Nat.div_one, List.getD_cons_zero]
      have := h.1
      omega
    | succ j =>
      have e : digit16 (pack16 (d :: ds)) (j + 1) = digit16 (pack16 ds) j := by
        unfold digit16
        simp only [pack16, Nat.pow_succ]
        rw [show 65536 ^ j * 65536 = 65536 * 65536 ^ j by omega, ← Nat.div_div_eq_div_mul]
        have h1 : (d + 65536 * pack16 ds) / 65536 = pack16 ds := by
          have := h.1
          omega
        rw [h1]
      rw [e, ih h.2 j]
      rfl

theorem pack16_zipAdd (ds es : List Nat) : pack16 (zipAdd ds es) = pack16 ds + pack16 es := by
  induction ds generalizing es with
  | nil => cases es <;> simp [zipAdd, pack16]
  | cons d ds ih =>
    cases es with
    | nil => simp [zipAdd, pack16]
    | cons e es =>
      simp only [zipAdd, pack16, ih]
      omega

theorem pack16_tab_add (f g : Nat → Nat) (n : Nat) :
    pack16 (tab f n) + pack16 (tab g n) = pack16 (tab (fun j => f j + g j) n) := by
  rw [← pack16_zipAdd, zipAdd_tab]

/-- Digit-wise subtraction (`g j <= f j`). -/
theorem pack16_tab_sub (f g : Nat → Nat) (n : Nat) (h : ∀ j, j < n → g j ≤ f j) :
    pack16 (tab f n) - pack16 (tab g n) = pack16 (tab (fun j => f j - g j) n) := by
  have e := pack16_tab_add (fun j => f j - g j) g n
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

theorem digit16_div (x j : Nat) : digit16 (x / 65536) j = digit16 x (j + 1) := by
  unfold digit16
  rw [Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm]

/-- Every number is the pack16 of its digits, modulo `65536 ^ n`. -/
theorem pack16_tab_digit_mod (n : Nat) : ∀ x, pack16 (tab (digit16 x) n) = x % 65536 ^ n := by
  induction n with
  | zero => intro x; simp [tab, pack16, Nat.mod_one]
  | succ n ih =>
    intro x
    simp only [tab, pack16]
    have h1 : (fun j => digit16 x (j + 1)) = digit16 (x / 65536) := by
      funext j; exact (digit16_div x j).symm
    rw [h1, ih, Nat.pow_succ, Nat.mul_comm (65536 ^ n) 65536, Nat.mod_mul]
    simp [digit16]

theorem pack16_tab_digit (x n : Nat) (hx : x < 65536 ^ n) : pack16 (tab (digit16 x) n) = x := by
  rw [pack16_tab_digit_mod, Nat.mod_eq_of_lt hx]

theorem pack16_lt (ds : List Nat) (h : Bounded 65536 ds) : pack16 ds < 65536 ^ ds.length := by
  induction ds with
  | nil => simp [pack16]
  | cons d ds ih =>
    simp only [pack16, List.length_cons, Nat.pow_succ]
    have := ih h.2
    have := h.1
    omega

/-- Bit `16 l + 15` of `n` is the top bit of digit `l`. -/
theorem testBit_digit16 (n l : Nat) : Nat.testBit n (16 * l + 15) = Nat.testBit (digit16 n l) 15 := by
  unfold digit16
  rw [show 65536 ^ l = 2 ^ (16 * l) by simp [Nat.pow_mul], ← Nat.shiftRight_eq_div_pow,
    show (65536 : Nat) = 2 ^ 16 by rfl, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
  try simp

theorem testBit_top16 (d : Nat) (hd : d < 65536) : Nat.testBit d 15 = decide (32768 ≤ d) := by
  rw [Nat.testBit_to_div_mod, Bool.eq_iff_iff, decide_eq_true_eq, decide_eq_true_eq]
  simp only [Nat.reducePow]
  omega

theorem swarOK16_spec (n : Nat) (a b : Nat → Nat) (A B BL HI : Nat)
    (hA : A = pack16 (tab a n)) (hB : B = pack16 (tab b n)) (hHI : HI = pack16 (tab (fun _ => 32768) n))
    (ha : ∀ l, l < n → a l ≤ 32768) (hb : ∀ l, l < n → b l < 32768)
    (h : swarOK A B BL HI = true) (l : Nat) (hl : l < n) :
    Nat.testBit BL (16 * l + 15) = true ∨ a l ≤ b l := by
  subst hHI
  unfold swarOK at h
  have heq := Nat.eq_of_beq_eq_true h
  subst hA hB
  rw [pack16_tab_add, pack16_tab_sub _ _ _ (fun j hj => by have := ha j hj; omega)] at heq
  -- bit 16 l + 15 of both sides
  have hbit := congrArg (fun x => Nat.testBit x (16 * l + 15)) heq
  simp only [Nat.testBit_or, Nat.testBit_and] at hbit
  have hhi : Nat.testBit (pack16 (tab (fun _ => 32768) n)) (16 * l + 15) = true := by
    rw [testBit_digit16, digit16_pack _ (tab_bounded _ _ _ (fun _ _ => by decide)) l, tab_getD _ _ l hl]
    decide
  have hz : Nat.testBit (pack16 (tab (fun j => b j + 32768 - a j) n)) (16 * l + 15) = decide (a l ≤ b l) := by
    rw [testBit_digit16, digit16_pack _ (tab_bounded _ _ _ (fun j hj => by have := hb j hj; omega)) l,
      tab_getD _ _ l hl, testBit_top16 _ (by have := hb l hl; omega)]
    rw [Bool.eq_iff_iff, decide_eq_true_eq, decide_eq_true_eq]
    have := ha l hl
    omega
  rw [hhi, hz, Bool.and_true] at hbit
  cases hd : decide (a l ≤ b l) with
  | true => exact Or.inr (of_decide_eq_true hd)
  | false =>
    rw [hd, Bool.false_or] at hbit
    exact Or.inl hbit

/-- A window of `n` 16-bit fields starting at field `a` of a table. -/
theorem winT_pack16 (T a n : Nat) :
    (T >>> (16 * a)) &&& (2 ^ (16 * n) - 1) = pack16 (tab (fun l => digit16 T (a + l)) n) := by
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]
  have e8 : ∀ m, (2 : Nat) ^ (16 * m) = 65536 ^ m := fun m => by simp [Nat.pow_mul]
  have h : (fun l => digit16 T (a + l)) = digit16 (T / 2 ^ (16 * a)) := by
    funext l
    unfold digit16
    rw [Nat.div_div_eq_div_mul, e8, ← Nat.pow_add]
  rw [h, pack16_tab_digit_mod, e8 n]

theorem pack16_tab_mul (c : Nat) (f : Nat → Nat) (n : Nat) : c * pack16 (tab f n) = pack16 (tab (fun j => c * f j) n) := by
  induction n generalizing f with
  | zero => simp [tab, pack16]
  | succ n ih =>
    simp only [tab, pack16]
    rw [Nat.mul_add, ← Nat.mul_assoc, Nat.mul_comm c 65536, Nat.mul_assoc, ih]

theorem pack16_tab_append (f : Nat → Nat) (n m : Nat) :
    pack16 (tab f (n + m)) = pack16 (tab f n) + 65536 ^ n * pack16 (tab (fun j => f (n + j)) m) := by
  induction n generalizing f with
  | zero => simp [tab, pack16]
  | succ n ih =>
    rw [Nat.succ_add]
    simp only [tab, pack16]
    rw [ih (fun j => f (j + 1))]
    simp only [Nat.pow_succ]
    have : (fun j => f (n + j + 1)) = fun j => f (n + 1 + j) := by funext j; congr 1; omega
    rw [this, Nat.mul_comm (65536 ^ n) 65536, Nat.mul_assoc]
    omega

/-- `[f 0, ..., f (n-1)]` repeated `m` times is the pack16 times `1 + 65536^n + ... + 65536^(n (m-1))`. -/
def repK16 (n : Nat) : Nat → Nat
  | 0 => 0
  | m + 1 => repK16 n m + 65536 ^ (n * m)

theorem pack16_tab_rep (f : Nat → Nat) (n : Nat) : ∀ m, pack16 (tab (fun l => f (l % n)) (n * m)) = pack16 (tab f n) * repK16 n m
  | 0 => by simp [tab, pack16, repK16]
  | m + 1 => by
    rw [Nat.mul_succ, pack16_tab_append, pack16_tab_rep f n m]
    have h2 : tab (fun j => f ((n * m + j) % n)) n = tab f n := by
      apply tab_congr; intro j hj
      rw [show n * m + j = j + n * m by omega, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]
    rw [h2, repK16, Nat.mul_add, Nat.mul_comm (pack16 (tab f n)) (65536 ^ (n * m))]

theorem digit16_lt (n j : Nat) : digit16 n j < 65536 := Nat.mod_lt _ (by decide)

/-- `P &&& HI = 0`, with `HI` the top bit of every field: every field of `P` is below 32768. -/
theorem digit16_lt_half_of_and (P n : Nat) (h : (P &&& pack16 (tab (fun _ => 32768) n)) = 0)
    (y : Nat) (hy : y < n) : digit16 P y < 32768 := by
  have hb : Nat.testBit (P &&& pack16 (tab (fun _ => 32768) n)) (16 * y + 15) = false := by
    rw [h]; simp
  rw [Nat.testBit_and, testBit_digit16, testBit_digit16,
    digit16_pack _ (tab_bounded _ _ _ (fun _ _ => by decide)) y, tab_getD _ _ y hy,
    show Nat.testBit 32768 15 = true by decide, Bool.and_true, testBit_top16 _ (digit16_lt _ _)] at hb
  simpa using hb

/-- Field-wise bound `digit16 P y + c < 32768` from two mask tests: no field of `P` has its top bit
set, and neither has any field of `P + c * ONE` (`ONE` is 1 in every field; `c <= 32767` so the
addition never carries).  With `c = 32767 - R` this is `digit16 P y <= R`. -/
theorem fields_lt_of_masks16 (P n c HI ONE : Nat) (hHI : HI = pack16 (tab (fun _ => 32768) n))
    (hONE : ONE = pack16 (tab (fun _ => 1) n)) (hc : c ≤ 32767)
    (h : (Nat.ble (P + 1) (65536 ^ n) && Nat.beq (P &&& HI) 0 && Nat.beq ((P + c * ONE) &&& HI) 0) = true)
    (y : Nat) (hy : y < n) : digit16 P y + c < 32768 := by
  subst hHI hONE
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨h0, h1⟩, h2⟩ := h
  have hP : P < 65536 ^ n := Nat.le_of_ble_eq_true h0
  have hlt : ∀ j, j < n → digit16 P j < 32768 := digit16_lt_half_of_and P n (Nat.eq_of_beq_eq_true h1)
  have hsum : pack16 (tab (digit16 P) n) + c * pack16 (tab (fun _ => 1) n) =
      pack16 (tab (fun j => digit16 P j + c) n) := by
    rw [pack16_tab_mul, pack16_tab_add]
    simp
  rw [pack16_tab_digit P n hP] at hsum
  have hbd : Bounded 65536 (tab (fun j => digit16 P j + c) n) :=
    tab_bounded _ _ _ (fun j hj => by have := hlt j hj; omega)
  have h2' := digit16_lt_half_of_and _ n (Nat.eq_of_beq_eq_true h2) y hy
  rw [hsum, digit16_pack _ hbd y, tab_getD _ _ y hy] at h2'
  exact h2'

/-- Field `m` of the `n`-field window of `T` starting at field `a`. -/
theorem digit16_winT (T a n m : Nat) (hm : m < n) : digit16 (winT T (16 * a) (16 * n)) m = digit16 T (a + m) := by
  unfold winT
  rw [winT_pack16, digit16_pack _ (tab_bounded _ _ _ (fun _ _ => digit16_lt _ _)), tab_getD _ _ m hm]

/-- Bit `16 f + 15` of a table of `n` fields replicated `m` times by multiplication with `repK16`. -/
theorem testBit_mul_rep16 (X n m f : Nat) (hX : X < 2 ^ (16 * n)) (hf : f < n * m) :
    Nat.testBit (X * repK16 n m) (16 * f + 15) = Nat.testBit X (16 * (f % n) + 15) := by
  have hX' : X < 65536 ^ n := by
    have e8 : (2 : Nat) ^ (16 * n) = 65536 ^ n := by simp [Nat.pow_mul]
    rw [← e8]; exact hX
  have h := pack16_tab_rep (digit16 X) n m
  rw [pack16_tab_digit X n hX'] at h
  rw [← h, testBit_digit16, digit16_pack _ (tab_bounded _ _ _ (fun _ _ => digit16_lt _ _)), tab_getD _ _ f hf,
    ← testBit_digit16]

/-- Geometric sum: `repK16 n m` is `(65536^(n m) - 1) / (65536^n - 1)`, so the kernel can compute a
replicator with one power and one division instead of reading it as a numeral. -/
theorem repK16_geom (n : Nat) : ∀ m, repK16 n m * (65536 ^ n - 1) + 1 = 65536 ^ (n * m)
  | 0 => by simp [repK16]
  | m + 1 => by
    have ih := repK16_geom n m
    have hB : 1 ≤ 65536 ^ n := Nat.pow_pos (by decide)
    simp only [repK16]
    rw [Nat.mul_succ, Nat.pow_add]
    generalize 65536 ^ (n * m) = A at ih ⊢
    generalize repK16 n m = r at ih ⊢
    generalize hBdef : 65536 ^ n = B at ih hB ⊢
    obtain ⟨c, rfl⟩ : ∃ c, B = c + 1 := ⟨B - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at ih ⊢
    rw [Nat.add_mul, Nat.mul_succ]
    omega

theorem repK16_eq_div (n m : Nat) (hn : 0 < n) : repK16 n m = (65536 ^ (n * m) - 1) / (65536 ^ n - 1) := by
  have h := repK16_geom n m
  have hpos : 0 < 65536 ^ n - 1 := by
    have : 65536 ≤ 65536 ^ n := by
      calc 65536 = 65536 ^ 1 := by rfl
        _ ≤ 65536 ^ n := Nat.pow_le_pow_right (by decide) hn
    omega
  exact (Nat.div_eq_of_eq_mul_left hpos (by omega)).symm

/-- Field-wise `digit16 Pt y + c <= digit16 St y` for all `n` fields from one packed comparison with
an empty blocking mask (`c * ONE` adds `c` to every field without carries). -/
theorem field_le_of_swarOK16 (n Pt St HI ONE c : Nat) (hP : Pt < 65536 ^ n) (hS : St < 65536 ^ n)
    (hHI : HI = pack16 (tab (fun _ => 32768) n)) (hONE : ONE = pack16 (tab (fun _ => 1) n))
    (ha : ∀ y, y < n → digit16 Pt y + c ≤ 32768) (hb : ∀ y, y < n → digit16 St y < 32768)
    (h : swarOK (Pt + c * ONE) St 0 HI = true) (y : Nat) (hy : y < n) : digit16 Pt y + c ≤ digit16 St y := by
  have hA : Pt + c * ONE = pack16 (tab (fun l => digit16 Pt l + c) n) := by
    have e := pack16_tab_digit Pt n hP
    conv => lhs; rw [← e]
    rw [hONE, pack16_tab_mul, pack16_tab_add]
    apply congrArg; apply tab_congr; intro j _; simp
  have hB : St = pack16 (tab (digit16 St) n) := (pack16_tab_digit St n hS).symm
  have key := swarOK16_spec n (fun l => digit16 Pt l + c) (digit16 St) _ _ 0 HI hA hB hHI ha hb h y hy
  simpa using key

end Snake9.WindowAutomaton
