import WindowAutomaton7Defs

/-!
# Witness-driven shard check of the seven-centre automaton (shard v2)

`check7In2W T c t0 t1 t2 ws wt` evaluates, for every source state `(t3, t4, t5)` and every new
count `s`, ONE disjunct of `check7In2 T c t0 t1 t2`, chosen by 4-bit codes in the literals `ws`
(per source) and `wt` (per transition).  A wrong code only makes the check fail.  All arithmetic
is written with the kernel's GMP primitives (`Nat.add`, `Nat.mul`, `Nat.sub`, `Nat.shiftRight`,
`Nat.land`, `Nat.beq`, `Nat.ble`) and the list recursions of `cntIdx6`/`symIdx` are unfolded.

Written by `milestones/25-k7-234/lean/scripts/gen_window_automaton7_v2.py`, which spells out the
index arithmetic and the case proofs; edit the script, not this file.
-/

namespace Snake9.WindowAutomaton

/-- 4-bit field `i` of `w`. -/
def code4 (w i : Nat) : Nat := Nat.land (Nat.shiftRight w (Nat.mul 4 i)) 15

/-- `y` if the bit `m` (a power of two) of `k` is set, else `x`. -/
def sel2 (k m : Nat) (x y : Bool) : Bool := cond (Nat.beq (Nat.land k m) 0) x y

/-- One of 16 Booleans, selected by the low four bits of `k` (lazy in the others). -/
def bsel4 (k : Nat) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : Bool) : Bool :=
  sel2 k 8
    (sel2 k 4
      (sel2 k 2 (sel2 k 1 x0 x1) (sel2 k 1 x2 x3))
      (sel2 k 2 (sel2 k 1 x4 x5) (sel2 k 1 x6 x7)))
    (sel2 k 4
      (sel2 k 2 (sel2 k 1 x8 x9) (sel2 k 1 x10 x11))
      (sel2 k 2 (sel2 k 1 x12 x13) (sel2 k 1 x14 x15)))

/-- The exclusion bit of the window `ds` with first count `s0`; `i` is the `symIdx` of the
other counts (the body of `forbBit6`). -/
def fb7 (T : Tables7) (ds : List Nat) (s0 i : Nat) : Bool :=
  Nat.beq (Nat.land (Nat.shiftRight (T.forb (T.wIdx (shapeCode (canon ds))) s0) i) 1) 1

/-- The step inequality, the potential rows `rs` (source) and `rd` (target) given. -/
def ineq7F (T : Tables7) (rs rd t2 t3 t4 t5 s : Nat) : Bool :=
  Nat.ble (Nat.add T.num (Nat.land (Nat.shiftRight rd (Nat.mul T.bits (Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.sub t3 1) 6) (Nat.sub t4 1)) 6) (Nat.sub t5 1)) 6) (Nat.sub s 1))))
      (Nat.sub (Nat.pow 2 T.bits) 1)))
    (Nat.add (Nat.mul T.den s) (Nat.land (Nat.shiftRight rs (Nat.mul T.bits (Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.sub t2 1) 6) (Nat.sub t3 1)) 6) (Nat.sub t4 1)) 6) (Nat.sub t5 1))))
      (Nat.sub (Nat.pow 2 T.bits) 1)))

/-- One transition: code 0 the inequality, `2 (w - 2) + 1` and `2 (w - 2) + 2` the window of
`w + 1` directions ending at the new vertex (forward, reversed; w = 2..7), 13 the H9 window. -/
def tr7F (T : Tables7) (c : List Nat) (rs rd t0 t1 t2 t3 t4 t5 s code : Nat) : Bool :=
  cond (Nat.beq code 0) (ineq7F T rs rd t2 t3 t4 t5 s) (bsel4 code false
    (fb7 T (c.drop 6) t5 s)
    (fb7 T (c.drop 6).reverse s t5)
    (fb7 T (c.drop 5) t4 (Nat.add (Nat.mul t5 7) s))
    (fb7 T (c.drop 5).reverse s (Nat.add (Nat.mul t5 7) t4))
    (fb7 T (c.drop 4) t3 (Nat.add (Nat.mul (Nat.add (Nat.mul t4 7) t5) 7) s))
    (fb7 T (c.drop 4).reverse s (Nat.add (Nat.mul (Nat.add (Nat.mul t5 7) t4) 7) t3))
    (fb7 T (c.drop 3) t2 (Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul t3 7) t4) 7) t5) 7) s))
    (fb7 T (c.drop 3).reverse s (Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul t5 7) t4) 7) t3) 7) t2))
    (fb7 T (c.drop 2) t1 (Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul t2 7) t3) 7) t4) 7) t5) 7) s))
    (fb7 T (c.drop 2).reverse s (Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul t5 7) t4) 7) t3) 7) t2) 7) t1))
    (fb7 T (c.drop 1) t0 (Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul t1 7) t2) 7) t3) 7) t4) 7) t5) 7) s))
    (fb7 T (c.drop 1).reverse s (Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul t5 7) t4) 7) t3) 7) t2) 7) t1) 7) t0))
    (wforbH T c [t0, t1, t2, t3, t4, t5, s]) false false)

/-- One source state: code 0 its transitions `go`, `2 (w - 2) + 1` and `2 (w - 2) + 2` its own
window of `w + 1` directions (forward, reversed; w = 2..6). -/
def src7F (T : Tables7) (h : List Nat) (t0 t1 t2 t3 t4 t5 code : Nat) (go : Bool) : Bool :=
  cond (Nat.beq code 0) go (bsel4 code false
    (fb7 T (h.drop 5) t4 t5)
    (fb7 T (h.drop 5).reverse t5 t4)
    (fb7 T (h.drop 4) t3 (Nat.add (Nat.mul t4 7) t5))
    (fb7 T (h.drop 4).reverse t5 (Nat.add (Nat.mul t4 7) t3))
    (fb7 T (h.drop 3) t2 (Nat.add (Nat.mul (Nat.add (Nat.mul t3 7) t4) 7) t5))
    (fb7 T (h.drop 3).reverse t5 (Nat.add (Nat.mul (Nat.add (Nat.mul t4 7) t3) 7) t2))
    (fb7 T (h.drop 2) t1 (Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul t2 7) t3) 7) t4) 7) t5))
    (fb7 T (h.drop 2).reverse t5 (Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul t4 7) t3) 7) t2) 7) t1))
    (fb7 T (h.drop 1) t0 (Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul t1 7) t2) 7) t3) 7) t4) 7) t5))
    (fb7 T (h.drop 1).reverse t5 (Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul t4 7) t3) 7) t2) 7) t1) 7) t0))
    false false false false false)

/-- Field of the source state `(t3, t4, t5)`: `(t3 - 1) * 36 + (t4 - 1) * 6 + (t5 - 1)`. -/
def srcIx (t3 t4 t5 : Nat) : Nat := Nat.sub (Nat.add (Nat.mul (Nat.add (Nat.mul t3 6) t4) 6) t5) 43

/-- The witness-driven form of `check7In2`: `ws` holds a 4-bit code per source state (field
`srcIx t3 t4 t5`, 216 fields), `wt` one per transition (field `6 * srcIx t3 t4 t5 + s - 1`,
1,296 fields). -/
def check7In2W (T : Tables7) (c : List Nat) (t0 t1 t2 ws wt : Nat) : Bool :=
  let rs := T.pot (T.pIdx (shapeCode (canon (c.take 8)))) t0 t1
  let rd := T.pot (T.pIdx (shapeCode (canon (c.drop 1)))) t1 t2
  allSym (fun t3 => allSym (fun t4 => allSym (fun t5 =>
    src7F T (c.take 8) t0 t1 t2 t3 t4 t5 (code4 ws (srcIx t3 t4 t5))
      (allSym (fun s => tr7F T c rs rd t0 t1 t2 t3 t4 t5 s
        (code4 wt (Nat.add (Nat.mul (srcIx t3 t4 t5) 6) (Nat.sub s 1))))))))

/-- `check7In2W` for every `t2`: block `t2 - 1` of `ws` (864 bits) and of `wt` (5,184 bits). -/
def check7InW (T : Tables7) (c : List Nat) (t0 t1 ws wt : Nat) : Bool :=
  allSym (fun t2 => check7In2W T c t0 t1 t2 (Nat.shiftRight ws (Nat.mul 864 (Nat.sub t2 1)))
    (Nat.shiftRight wt (Nat.mul 5184 (Nat.sub t2 1))))

/-- `check7InW` for every `t1`: block `t1 - 1` of `ws` (5,184 bits) and of `wt` (31,104 bits).
The `inducedPattern` test of `check7At` is not evaluated (the shards use it on induced labels). -/
def check7AtW (T : Tables7) (c : List Nat) (t0 ws wt : Nat) : Bool :=
  allSym (fun t1 => check7InW T c t0 t1 (Nat.shiftRight ws (Nat.mul 5184 (Nat.sub t1 1)))
    (Nat.shiftRight wt (Nat.mul 31104 (Nat.sub t1 1))))

/-! ### Soundness -/

theorem symIdx_eq1 (x0 : Nat) :
    symIdx [x0] 0 = x0 := by
  simp only [symIdx, Nat.zero_mul, Nat.zero_add]; try rfl

theorem symIdx_eq2 (x0 x1 : Nat) :
    symIdx [x0, x1] 0 = Nat.add (Nat.mul x0 7) x1 := by
  simp only [symIdx, Nat.zero_mul, Nat.zero_add]; try rfl

theorem symIdx_eq3 (x0 x1 x2 : Nat) :
    symIdx [x0, x1, x2] 0 = Nat.add (Nat.mul (Nat.add (Nat.mul x0 7) x1) 7) x2 := by
  simp only [symIdx, Nat.zero_mul, Nat.zero_add]; try rfl

theorem symIdx_eq4 (x0 x1 x2 x3 : Nat) :
    symIdx [x0, x1, x2, x3] 0 = Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul x0 7) x1) 7) x2) 7) x3 := by
  simp only [symIdx, Nat.zero_mul, Nat.zero_add]; try rfl

theorem symIdx_eq5 (x0 x1 x2 x3 x4 : Nat) :
    symIdx [x0, x1, x2, x3, x4] 0 = Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul x0 7) x1) 7) x2) 7) x3) 7) x4 := by
  simp only [symIdx, Nat.zero_mul, Nat.zero_add]; try rfl

theorem symIdx_eq6 (x0 x1 x2 x3 x4 x5 : Nat) :
    symIdx [x0, x1, x2, x3, x4, x5] 0 = Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul x0 7) x1) 7) x2) 7) x3) 7) x4) 7) x5 := by
  simp only [symIdx, Nat.zero_mul, Nat.zero_add]; try rfl

theorem nat_beq_eq (a b : Nat) : Nat.beq a b = (a == b) := by
  cases h : Nat.beq a b
  · have := Nat.ne_of_beq_eq_false h; simp [this]
  · have := Nat.eq_of_beq_eq_true h; simp [this]

theorem nat_ble_eq (a b : Nat) : Nat.ble a b = decide (a ≤ b) := by
  cases h : Nat.ble a b
  · have : ¬ a ≤ b := fun hle => by simp [Nat.ble_eq_true_of_le hle] at h
    simp [this]
  · simp [Nat.le_of_ble_eq_true h]

theorem fb7_eq (T : Tables7) (ds : List Nat) (s0 : Nat) (rest : List Nat) :
    fb7 T ds s0 (symIdx rest 0) = wforbA6 T.k6 ds (s0 :: rest) := by
  unfold fb7 wforbA6 forbBit6
  rw [nat_beq_eq]
  rfl

theorem cntIdx4_eq (a b c d : Nat) :
    cntIdx6 [a, b, c, d] 0 = Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.sub a 1) 6) (Nat.sub b 1)) 6) (Nat.sub c 1)) 6) (Nat.sub d 1) := by
  simp only [cntIdx6, Nat.zero_mul, Nat.zero_add]; rfl

theorem sel2_sound {k m : Nat} {x y : Bool} {P Q : Prop} (hx : x = true → P) (hy : y = true → Q)
    (h : sel2 k m x y = true) : P ∨ Q := by
  unfold sel2 at h
  cases hb : Nat.beq (Nat.land k m) 0 <;> rw [hb] at h <;> simp only [cond_true, cond_false] at h
  · exact Or.inr (hy h)
  · exact Or.inl (hx h)

theorem bsel4_sound {k : Nat} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : Bool}
    (h : bsel4 k x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 = true) :
    (((x0 = true ∨ x1 = true) ∨ (x2 = true ∨ x3 = true)) ∨
      ((x4 = true ∨ x5 = true) ∨ (x6 = true ∨ x7 = true))) ∨
    (((x8 = true ∨ x9 = true) ∨ (x10 = true ∨ x11 = true)) ∨
      ((x12 = true ∨ x13 = true) ∨ (x14 = true ∨ x15 = true))) :=
  sel2_sound
    (sel2_sound (sel2_sound (sel2_sound id id) (sel2_sound id id))
      (sel2_sound (sel2_sound id id) (sel2_sound id id)))
    (sel2_sound (sel2_sound (sel2_sound id id) (sel2_sound id id))
      (sel2_sound (sel2_sound id id) (sel2_sound id id))) h

theorem ineq7F_sound (T : Tables7) (c : List Nat) (rs rd t0 t1 t2 t3 t4 t5 s : Nat)
    (hrs : rs = T.pot (T.pIdx (shapeCode (canon (c.take 8)))) t0 t1)
    (hrd : rd = T.pot (T.pIdx (shapeCode (canon (c.drop 1)))) t1 t2)
    (h : ineq7F T rs rd t2 t3 t4 t5 s = true) :
    decide (T.num + pot7 T (c.drop 1) [t1, t2, t3, t4, t5, s] ≤
      T.den * s + pot7 T (c.take 8) [t0, t1, t2, t3, t4, t5]) = true := by
  have e1 : pot7 T (c.drop 1) [t1, t2, t3, t4, t5, s] =
      Nat.land (Nat.shiftRight rd (Nat.mul T.bits (Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.sub t3 1) 6) (Nat.sub t4 1)) 6) (Nat.sub t5 1)) 6) (Nat.sub s 1)))) (Nat.sub (Nat.pow 2 T.bits) 1) := by
    rw [hrd]; simp only [pot7, potAt7, cntIdx4_eq]; rfl
  have e2 : pot7 T (c.take 8) [t0, t1, t2, t3, t4, t5] =
      Nat.land (Nat.shiftRight rs (Nat.mul T.bits (Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.sub t2 1) 6) (Nat.sub t3 1)) 6) (Nat.sub t4 1)) 6) (Nat.sub t5 1)))) (Nat.sub (Nat.pow 2 T.bits) 1) := by
    rw [hrs]; simp only [pot7, potAt7, cntIdx4_eq]; rfl
  unfold ineq7F at h
  rw [nat_ble_eq] at h
  rw [e1, e2]
  exact h

/-- A selected transition disjunct implies the transition disjunction of `check7In2`. -/
theorem tr7F_sound (T : Tables7) (c : List Nat) (rs rd t0 t1 t2 t3 t4 t5 s code : Nat)
    (hrs : rs = T.pot (T.pIdx (shapeCode (canon (c.take 8)))) t0 t1)
    (hrd : rd = T.pot (T.pIdx (shapeCode (canon (c.drop 1)))) t1 t2)
    (h : tr7F T c rs rd t0 t1 t2 t3 t4 t5 s code = true) :
    (wforb6 T.k6 (c.drop 6) [t5, s] || wforb6 T.k6 (c.drop 5) [t4, t5, s] ||
      wforb6 T.k6 (c.drop 4) [t3, t4, t5, s] || wforb6 T.k6 (c.drop 3) [t2, t3, t4, t5, s] ||
      wforb6 T.k6 (c.drop 2) [t1, t2, t3, t4, t5, s] ||
      wforb6 T.k6 (c.drop 1) [t0, t1, t2, t3, t4, t5, s] ||
      wforbH T c [t0, t1, t2, t3, t4, t5, s] ||
      decide (T.num + pot7 T (c.drop 1) [t1, t2, t3, t4, t5, s] ≤
        T.den * s + pot7 T (c.take 8) [t0, t1, t2, t3, t4, t5])) = true := by
  unfold tr7F at h
  cases hb : Nat.beq code 0 <;> rw [hb] at h <;> simp only [cond_true, cond_false] at h
  · rcases bsel4_sound h with ((((h | h) | (h | h)) | ((h | h) | (h | h))) |
      (((h | h) | (h | h)) | ((h | h) | (h | h))))
    · simp at h
    · have h' : wforbA6 T.k6 (c.drop 6) [t5, s] = true := by
        have e := fb7_eq T (c.drop 6) t5 [s]
        rw [symIdx_eq1] at e
        rw [e] at h
        exact h
      simp only [Bool.or_eq_true, wforb6, h', true_or, or_true]
    · have h' : wforbA6 T.k6 (c.drop 6).reverse [t5, s].reverse = true := by
        have e := fb7_eq T (c.drop 6).reverse s [t5]
        rw [symIdx_eq1] at e
        rw [e] at h
        exact h
      simp only [Bool.or_eq_true, wforb6, h', true_or, or_true]
    · have h' : wforbA6 T.k6 (c.drop 5) [t4, t5, s] = true := by
        have e := fb7_eq T (c.drop 5) t4 [t5, s]
        rw [symIdx_eq2] at e
        rw [e] at h
        exact h
      simp only [Bool.or_eq_true, wforb6, h', true_or, or_true]
    · have h' : wforbA6 T.k6 (c.drop 5).reverse [t4, t5, s].reverse = true := by
        have e := fb7_eq T (c.drop 5).reverse s [t5, t4]
        rw [symIdx_eq2] at e
        rw [e] at h
        exact h
      simp only [Bool.or_eq_true, wforb6, h', true_or, or_true]
    · have h' : wforbA6 T.k6 (c.drop 4) [t3, t4, t5, s] = true := by
        have e := fb7_eq T (c.drop 4) t3 [t4, t5, s]
        rw [symIdx_eq3] at e
        rw [e] at h
        exact h
      simp only [Bool.or_eq_true, wforb6, h', true_or, or_true]
    · have h' : wforbA6 T.k6 (c.drop 4).reverse [t3, t4, t5, s].reverse = true := by
        have e := fb7_eq T (c.drop 4).reverse s [t5, t4, t3]
        rw [symIdx_eq3] at e
        rw [e] at h
        exact h
      simp only [Bool.or_eq_true, wforb6, h', true_or, or_true]
    · have h' : wforbA6 T.k6 (c.drop 3) [t2, t3, t4, t5, s] = true := by
        have e := fb7_eq T (c.drop 3) t2 [t3, t4, t5, s]
        rw [symIdx_eq4] at e
        rw [e] at h
        exact h
      simp only [Bool.or_eq_true, wforb6, h', true_or, or_true]
    · have h' : wforbA6 T.k6 (c.drop 3).reverse [t2, t3, t4, t5, s].reverse = true := by
        have e := fb7_eq T (c.drop 3).reverse s [t5, t4, t3, t2]
        rw [symIdx_eq4] at e
        rw [e] at h
        exact h
      simp only [Bool.or_eq_true, wforb6, h', true_or, or_true]
    · have h' : wforbA6 T.k6 (c.drop 2) [t1, t2, t3, t4, t5, s] = true := by
        have e := fb7_eq T (c.drop 2) t1 [t2, t3, t4, t5, s]
        rw [symIdx_eq5] at e
        rw [e] at h
        exact h
      simp only [Bool.or_eq_true, wforb6, h', true_or, or_true]
    · have h' : wforbA6 T.k6 (c.drop 2).reverse [t1, t2, t3, t4, t5, s].reverse = true := by
        have e := fb7_eq T (c.drop 2).reverse s [t5, t4, t3, t2, t1]
        rw [symIdx_eq5] at e
        rw [e] at h
        exact h
      simp only [Bool.or_eq_true, wforb6, h', true_or, or_true]
    · have h' : wforbA6 T.k6 (c.drop 1) [t0, t1, t2, t3, t4, t5, s] = true := by
        have e := fb7_eq T (c.drop 1) t0 [t1, t2, t3, t4, t5, s]
        rw [symIdx_eq6] at e
        rw [e] at h
        exact h
      simp only [Bool.or_eq_true, wforb6, h', true_or, or_true]
    · have h' : wforbA6 T.k6 (c.drop 1).reverse [t0, t1, t2, t3, t4, t5, s].reverse = true := by
        have e := fb7_eq T (c.drop 1).reverse s [t5, t4, t3, t2, t1, t0]
        rw [symIdx_eq6] at e
        rw [e] at h
        exact h
      simp only [Bool.or_eq_true, wforb6, h', true_or, or_true]
    · simp only [Bool.or_eq_true, h, true_or, or_true]
    · simp at h
    · simp at h
  · have h' := ineq7F_sound T c rs rd t0 t1 t2 t3 t4 t5 s hrs hrd h
    simp only [Bool.or_eq_true, h', or_true]

/-- A selected source disjunct: the transitions, or an own window of the source state. -/
theorem src7F_sound (T : Tables7) (h : List Nat) (t0 t1 t2 t3 t4 t5 code : Nat) (go : Bool)
    (hh : src7F T h t0 t1 t2 t3 t4 t5 code go = true) :
    go = true ∨ own7 T h t0 t1 t2 t3 t4 t5 = true := by
  unfold src7F at hh
  cases hb : Nat.beq code 0 <;> rw [hb] at hh <;> simp only [cond_true, cond_false] at hh
  · rcases bsel4_sound hh with ((((hh | hh) | (hh | hh)) | ((hh | hh) | (hh | hh))) |
      (((hh | hh) | (hh | hh)) | ((hh | hh) | (hh | hh))))
    · simp at hh
    · have h' : wforbA6 T.k6 (h.drop 5) [t4, t5] = true := by
        have e := fb7_eq T (h.drop 5) t4 [t5]
        rw [symIdx_eq1] at e
        rw [e] at hh
        exact hh
      right; simp only [own7, Bool.or_eq_true, wforb6, h', true_or, or_true]
    · have h' : wforbA6 T.k6 (h.drop 5).reverse [t4, t5].reverse = true := by
        have e := fb7_eq T (h.drop 5).reverse t5 [t4]
        rw [symIdx_eq1] at e
        rw [e] at hh
        exact hh
      right; simp only [own7, Bool.or_eq_true, wforb6, h', true_or, or_true]
    · have h' : wforbA6 T.k6 (h.drop 4) [t3, t4, t5] = true := by
        have e := fb7_eq T (h.drop 4) t3 [t4, t5]
        rw [symIdx_eq2] at e
        rw [e] at hh
        exact hh
      right; simp only [own7, Bool.or_eq_true, wforb6, h', true_or, or_true]
    · have h' : wforbA6 T.k6 (h.drop 4).reverse [t3, t4, t5].reverse = true := by
        have e := fb7_eq T (h.drop 4).reverse t5 [t4, t3]
        rw [symIdx_eq2] at e
        rw [e] at hh
        exact hh
      right; simp only [own7, Bool.or_eq_true, wforb6, h', true_or, or_true]
    · have h' : wforbA6 T.k6 (h.drop 3) [t2, t3, t4, t5] = true := by
        have e := fb7_eq T (h.drop 3) t2 [t3, t4, t5]
        rw [symIdx_eq3] at e
        rw [e] at hh
        exact hh
      right; simp only [own7, Bool.or_eq_true, wforb6, h', true_or, or_true]
    · have h' : wforbA6 T.k6 (h.drop 3).reverse [t2, t3, t4, t5].reverse = true := by
        have e := fb7_eq T (h.drop 3).reverse t5 [t4, t3, t2]
        rw [symIdx_eq3] at e
        rw [e] at hh
        exact hh
      right; simp only [own7, Bool.or_eq_true, wforb6, h', true_or, or_true]
    · have h' : wforbA6 T.k6 (h.drop 2) [t1, t2, t3, t4, t5] = true := by
        have e := fb7_eq T (h.drop 2) t1 [t2, t3, t4, t5]
        rw [symIdx_eq4] at e
        rw [e] at hh
        exact hh
      right; simp only [own7, Bool.or_eq_true, wforb6, h', true_or, or_true]
    · have h' : wforbA6 T.k6 (h.drop 2).reverse [t1, t2, t3, t4, t5].reverse = true := by
        have e := fb7_eq T (h.drop 2).reverse t5 [t4, t3, t2, t1]
        rw [symIdx_eq4] at e
        rw [e] at hh
        exact hh
      right; simp only [own7, Bool.or_eq_true, wforb6, h', true_or, or_true]
    · have h' : wforbA6 T.k6 (h.drop 1) [t0, t1, t2, t3, t4, t5] = true := by
        have e := fb7_eq T (h.drop 1) t0 [t1, t2, t3, t4, t5]
        rw [symIdx_eq5] at e
        rw [e] at hh
        exact hh
      right; simp only [own7, Bool.or_eq_true, wforb6, h', true_or, or_true]
    · have h' : wforbA6 T.k6 (h.drop 1).reverse [t0, t1, t2, t3, t4, t5].reverse = true := by
        have e := fb7_eq T (h.drop 1).reverse t5 [t4, t3, t2, t1, t0]
        rw [symIdx_eq5] at e
        rw [e] at hh
        exact hh
      right; simp only [own7, Bool.or_eq_true, wforb6, h', true_or, or_true]
    · simp at hh
    · simp at hh
    · simp at hh
    · simp at hh
    · simp at hh
  · exact Or.inl hh

/-- **Bridge**: the witness-driven check implies the step test of `check7In2`, whatever the
codes `ws`, `wt`. -/
theorem check7In2_of_W (T : Tables7) (c : List Nat) (t0 t1 t2 ws wt : Nat)
    (h : check7In2W T c t0 t1 t2 ws wt = true) : check7In2 T c t0 t1 t2 = true := by
  unfold check7In2
  unfold check7In2W at h
  refine allSym_of_forall _ (fun t3 h3 h3' => allSym_of_forall _ (fun t4 h4 h4' =>
    allSym_of_forall _ (fun t5 h5 h5' => ?_)))
  have hs := allSym_spec _ (allSym_spec _ (allSym_spec _ h t3 h3 h3') t4 h4 h4') t5 h5 h5'
  rcases src7F_sound _ _ _ _ _ _ _ _ _ _ hs with hg | ho
  · refine Bool.or_eq_true_iff.2 (Or.inr (allSym_of_forall _ (fun s hs1 hs6 => ?_)))
    exact tr7F_sound T c _ _ t0 t1 t2 t3 t4 t5 s _ rfl rfl (allSym_spec _ hg s hs1 hs6)
  · exact Bool.or_eq_true_iff.2 (Or.inl ho)

theorem check7In_of_W (T : Tables7) (c : List Nat) (t0 t1 ws wt : Nat)
    (h : check7InW T c t0 t1 ws wt = true) : check7In T c t0 t1 = true := by
  unfold check7In
  exact allSym_of_forall _ (fun t2 h1 h6 => check7In2_of_W _ _ _ _ _ _ _ (allSym_spec _ h t2 h1 h6))

/-- **Bridge** used by the shards: the witness-driven check of one label implies `check7At`. -/
theorem check7At_of_W (T : Tables7) (c : List Nat) (t0 ws wt : Nat)
    (h : check7AtW T c t0 ws wt = true) : check7At T c t0 = true := by
  unfold check7At
  exact Bool.or_eq_true_iff.2 (Or.inr (allSym_of_forall _ (fun t1 h1 h6 =>
    check7In_of_W _ _ _ _ _ _ (allSym_spec _ h t1 h1 h6))))

end Snake9.WindowAutomaton

#print axioms Snake9.WindowAutomaton.check7In2_of_W
#print axioms Snake9.WindowAutomaton.check7In_of_W
#print axioms Snake9.WindowAutomaton.check7At_of_W
