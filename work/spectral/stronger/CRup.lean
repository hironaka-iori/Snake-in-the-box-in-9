import FastRup
/-!
# CRup: reflective RUP blocks over a segmented clause database

Clause masks use the `FastRup` layout (`msat`, `stepF`, `finF`, `start`, `step_sound`, `close`).
A *database* `D : List Nat` is a list of *segments*; a segment packs 32 masks in slots of `S`
bits, and slot `j` of `D` is `getL S D j` (segment `j / 32`, slot `j % 32` in it).
`SatL τ W S D n` says that the first `n` slots of `D` are satisfied.

A block of RUP steps is checked by **one** kernel evaluation `sl … = true`: step `k` derives
slot `n + k` from hints that are slot indices `< n + k`.  A step is one packed `Nat`: the hint
count in bits `0..15`, a tag in bits `16..63`, and the hints above bit 64 (fields of `w` bits
holding `slot + 1`, first hint lowest).  So a proof term stores about `w` bits per hint plus
one list cell per step; the unit-propagation states are computed, never stored.

Kernel-cost notes (they do not affect soundness):
* the kernel caches `whnf` by expression; a hint index is turned into a literal by a
  `Nat.rec` case split, so `getL S D j` is evaluated once per distinct slot and per block;
* segments keep every intermediate `Nat` small (a flat database made the kernel cache one
  shifted copy of the whole database per distinct slot);
* the kernel hashes a `Nat` literal by its low 64 bits, hence the per-step tag.

Soundness: `hl_sound`, `sl_sound`, `sat_lapp`, `sat_lapp0`, `sel_sound` below.
-/
namespace CRup
open FastRup

/-- Slot `i` (width `S` bits) of the segment `d`. -/
def get (S d i : Nat) : Nat :=
  Nat.land (Nat.shiftRight d (Nat.mul i S)) (Nat.sub (Nat.shiftLeft 1 S) 1)

/-- `D` without its first `k` entries.  `dropN D (k+1)` is the tail of `dropN D k`, so the
kernel's cache shares the walk between segment lookups. -/
noncomputable def dropN (D : List Nat) (k : Nat) : List Nat :=
  Nat.rec (motive := fun _ => List Nat) D
    (fun _ ih => List.rec (motive := fun _ => List Nat) [] (fun _ t _ => t) ih) k

/-- Entry `k` of a list (`0` past the end), by plain recursors. -/
noncomputable def nth (D : List Nat) (k : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun a _ _ => a) (dropN D k)

/-- Slot `j` of the database `D` (32 slots per segment).  The segment index is case split so
that the kernel sees it as a literal (and caches the segment lookup). -/
noncomputable def getL (S : Nat) (D : List Nat) (j : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (get S (nth D 0) (Nat.land j 31))
    (fun k _ => get S (nth D (Nat.succ k)) (Nat.land j 31)) (Nat.shiftRight j 5)

/-- The first `n` slots of `D` are satisfied by `τ`. -/
def SatL (τ : Nat → Bool) (W S : Nat) (D : List Nat) (n : Nat) : Prop :=
  ∀ j, j < n → msat τ W (getL S D j)

/-- The hint loop of one step: `k` more hints follow the current one, which is the lowest
field of `hs`.  Each hint `j` must be an earlier slot (`j < n`); the last one must be a
conflict, the others propagate. -/
noncomputable def hl (W S : Nat) (D : List Nat) (n w M : Nat) : Nat → Nat → Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Bool)
    (fun hs F => Nat.rec (motive := fun _ => Bool) false
      (fun j _ => Bool.rec (motive := fun _ => Bool) false (finF W F (getL S D j)) (Nat.ble (Nat.succ j) n))
      (Nat.land hs M))
    (fun _ ih hs F => Nat.rec (motive := fun _ => Bool) false
      (fun j _ => Bool.rec (motive := fun _ => Bool) false
        (ih (Nat.shiftRight hs w) (stepF W F (getL S D j))) (Nat.ble (Nat.succ j) n))
      (Nat.land hs M))

/-- The step loop: step `k` of the list derives slot `n + k`. -/
noncomputable def sl (W S : Nat) (D : List Nat) (w M : Nat) (l : List Nat) (n : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun hs _ ih n => and (hl W S D n w M (Nat.sub (Nat.land hs 65535) 1) (Nat.shiftRight hs 64)
      (Nat.lor (getL S D n) pad)) (ih (Nat.succ n))) l n

/-! ### Soundness of the loops -/

theorem hl_sound {τ : Nat → Bool} {W S : Nat} {D : List Nat} {n w M : Nat} (hd : SatL τ W S D n) :
    ∀ k hs F, Inv τ W F → hl W S D n w M k hs F = true → False
  | 0, hs, F, hF, h => by
    change Nat.rec (motive := fun _ => Bool) false
      (fun j _ => Bool.rec (motive := fun _ => Bool) false (finF W F (getL S D j)) (Nat.ble (Nat.succ j) n))
      (Nat.land hs M) = true at h
    cases hx : Nat.land hs M with
    | zero => rw [hx] at h; exact Bool.false_ne_true h
    | succ j =>
      rw [hx] at h
      change Bool.rec (motive := fun _ => Bool) false (finF W F (getL S D j)) (Nat.ble (Nat.succ j) n) = true at h
      cases hb : Nat.ble (Nat.succ j) n with
      | false => rw [hb] at h; exact Bool.false_ne_true h
      | true => rw [hb] at h; exact close (hd j (Nat.le_of_ble_eq_true hb)) hF h
  | f + 1, hs, F, hF, h => by
    change Nat.rec (motive := fun _ => Bool) false
      (fun j _ => Bool.rec (motive := fun _ => Bool) false
        (hl W S D n w M f (Nat.shiftRight hs w) (stepF W F (getL S D j))) (Nat.ble (Nat.succ j) n))
      (Nat.land hs M) = true at h
    cases hx : Nat.land hs M with
    | zero => rw [hx] at h; exact Bool.false_ne_true h
    | succ j =>
      rw [hx] at h
      change Bool.rec (motive := fun _ => Bool) false
        (hl W S D n w M f (Nat.shiftRight hs w) (stepF W F (getL S D j))) (Nat.ble (Nat.succ j) n) = true at h
      cases hb : Nat.ble (Nat.succ j) n with
      | false => rw [hb] at h; exact Bool.false_ne_true h
      | true =>
        rw [hb] at h
        exact hl_sound hd f _ _ (step_sound (hd j (Nat.le_of_ble_eq_true hb)) hF) h

theorem sat_succ {τ : Nat → Bool} {W S : Nat} {D : List Nat} {n : Nat} (h : SatL τ W S D n)
    (hn : msat τ W (getL S D n)) : SatL τ W S D (Nat.succ n) := by
  intro i hi
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | hi
  · exact h i hi
  · rw [hi]; exact hn

theorem sat_zero {τ : Nat → Bool} {W S : Nat} {D : List Nat} : SatL τ W S D 0 :=
  fun _ h => absurd h (Nat.not_lt_zero _)

theorem sl_sound {τ : Nat → Bool} {W S : Nat} {D : List Nat} {w M : Nat} :
    ∀ (l : List Nat) (n : Nat), SatL τ W S D n → sl W S D w M l n = true →
      SatL τ W S D (n + l.length)
  | [], n, hd, _ => hd
  | hs :: l, n, hd, h => by
    change and (hl W S D n w M (Nat.sub (Nat.land hs 65535) 1) (Nat.shiftRight hs 64) (Nat.lor (getL S D n) pad))
      (sl W S D w M l (Nat.succ n)) = true at h
    rw [Bool.and_eq_true] at h
    have hn : msat τ W (getL S D n) :=
      Classical.byContradiction fun hn => hl_sound hd _ _ _ (start hn) h.1
    have := sl_sound l (Nat.succ n) (sat_succ hd hn) h.2
    rw [List.length_cons, show n + (l.length + 1) = Nat.succ n + l.length by omega]; exact this

/-! ### Appending databases -/

/-- `D₁` followed by `D₂` (plain recursor, for the kernel). -/
noncomputable def lapp (D₁ D₂ : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) D₂ (fun a _ ih => a :: ih) D₁

theorem dropN_eq (D : List Nat) : ∀ k, dropN D k = D.drop k
  | 0 => rfl
  | k + 1 => by
    show List.rec (motive := fun _ => List Nat) [] (fun _ t _ => t) (dropN D k) = _
    rw [dropN_eq D k, ← List.tail_drop]
    cases D.drop k <;> rfl

theorem nth_cons_succ (a : Nat) (t : List Nat) (k : Nat) : nth (a :: t) (k + 1) = nth t k := by
  unfold nth; rw [dropN_eq, dropN_eq]; rfl

theorem lapp_cons (a : Nat) (t D : List Nat) : lapp (a :: t) D = a :: lapp t D := rfl

theorem nth_lapp_lt : ∀ (D₁ D₂ : List Nat) (k : Nat), k < D₁.length → nth (lapp D₁ D₂) k = nth D₁ k
  | [], _, _, h => absurd h (Nat.not_lt_zero _)
  | _ :: _, _, 0, _ => rfl
  | a :: t, D₂, k + 1, h => by
    rw [lapp_cons, nth_cons_succ, nth_cons_succ]
    exact nth_lapp_lt t D₂ k (by simp at h; omega)

theorem nth_lapp_add : ∀ (D₁ D₂ : List Nat) (k : Nat), nth (lapp D₁ D₂) (D₁.length + k) = nth D₂ k
  | [], _, k => by simp [lapp]
  | a :: t, D₂, k => by
    rw [lapp_cons, List.length_cons, show t.length + 1 + k = (t.length + k) + 1 by omega, nth_cons_succ]
    exact nth_lapp_add t D₂ k

theorem getL_eq (S : Nat) (D : List Nat) (j : Nat) : getL S D j = get S (nth D (j / 32)) (j % 32) := by
  have h1 : Nat.shiftRight j 5 = j / 32 := Nat.shiftRight_eq_div_pow j 5
  have h2 : Nat.land j 31 = j % 32 := Nat.and_two_pow_sub_one_eq_mod j 5
  unfold getL
  rw [h1, h2]
  cases j / 32 <;> rfl

theorem getL_lapp_lt {S : Nat} {D₁ D₂ : List Nat} {j : Nat} (h : j < 32 * D₁.length) :
    getL S (lapp D₁ D₂) j = getL S D₁ j := by
  rw [getL_eq, getL_eq, nth_lapp_lt _ _ _ (by omega)]

theorem getL_lapp_add {S : Nat} {D₁ D₂ : List Nat} (i : Nat) :
    getL S (lapp D₁ D₂) (32 * D₁.length + i) = getL S D₂ i := by
  rw [getL_eq, getL_eq, show (32 * D₁.length + i) / 32 = D₁.length + i / 32 by omega,
    show (32 * D₁.length + i) % 32 = i % 32 by omega, nth_lapp_add]

theorem sat_lapp {τ : Nat → Bool} {W S : Nat} {D₁ D₂ : List Nat} {n₁ n₂ : Nat}
    (h₁ : SatL τ W S D₁ n₁) (h₂ : SatL τ W S D₂ n₂)
    (hn : Nat.beq n₁ (Nat.mul 32 (List.length D₁)) = true) : SatL τ W S (lapp D₁ D₂) (n₁ + n₂) := by
  have e : n₁ = 32 * D₁.length := Nat.eq_of_beq_eq_true hn
  intro j hj
  by_cases h : j < n₁
  · rw [getL_lapp_lt (by omega)]; exact h₁ j h
  · obtain ⟨i, rfl⟩ : ∃ i, j = 32 * D₁.length + i := ⟨j - 32 * D₁.length, by omega⟩
    rw [getL_lapp_add]; exact h₂ i (by omega)

theorem sat_lapp0 {τ : Nat → Bool} {W S : Nat} {D₁ : List Nat} {n : Nat} (D₂ : List Nat)
    (h₁ : SatL τ W S D₁ n) (hn : Nat.ble n (Nat.mul 32 (List.length D₁)) = true) :
    SatL τ W S (lapp D₁ D₂) n := by
  have e : n ≤ 32 * D₁.length := Nat.le_of_ble_eq_true hn
  intro j hj
  rw [getL_lapp_lt (by omega)]; exact h₁ j hj

/-! ### Padding and exports -/

/-- A tautology (`v₀ ∨ ¬v₀`), used to pad databases to whole segments. -/
def taut (W : Nat) : Nat := Nat.lor (Nat.shiftLeft 1 64) (Nat.shiftLeft 1 (Nat.add 64 W))

theorem msat_taut {τ : Nat → Bool} {W : Nat} (hW : Nat.ble 1 W = true) : msat τ W (taut W) := by
  have hW' : 1 ≤ W := Nat.le_of_ble_eq_true hW
  cases h : τ 0
  · refine ⟨64 + W, ?_, ?_⟩
    · show (1 <<< 64 ||| 1 <<< (64 + W)).testBit (64 + W) = true
      rw [Nat.testBit_or, Nat.one_shiftLeft, Nat.one_shiftLeft, Nat.testBit_two_pow_self, Bool.or_true]
    · unfold litT
      rw [if_neg (by omega), if_neg (by omega), if_pos (by omega), show 64 + W - 64 - W = 0 by omega, h]; rfl
  · refine ⟨64, ?_, ?_⟩
    · show (1 <<< 64 ||| 1 <<< (64 + W)).testBit 64 = true
      rw [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow_self, Bool.true_or]
    · unfold litT
      rw [if_neg (by omega), if_pos (by omega), show 64 - 64 = 0 by omega, h]

/-- `E` holds, in slots `j, j+1, …`, for each entry `s` of `l`: slot `s - 1` (`< n`) of `D`,
or a tautology (`s = 0`). -/
noncomputable def selOK (W S : Nat) (D : List Nat) (n : Nat) (E : List Nat) (l : List Nat) (j : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun s _ ih j => and
      (Nat.rec (motive := fun _ => Bool) (Nat.beq (getL S E j) (taut W))
        (fun s' _ => and (Nat.ble (Nat.succ s') n) (Nat.beq (getL S E j) (getL S D s'))) s)
      (ih (Nat.succ j))) l j

theorem sel_sound {τ : Nat → Bool} {W S : Nat} {D : List Nat} {n : Nat} {E : List Nat}
    (hW : Nat.ble 1 W = true) (hd : SatL τ W S D n) :
    ∀ (l : List Nat) (j : Nat), SatL τ W S E j → selOK W S D n E l j = true →
      SatL τ W S E (j + l.length)
  | [], _, hE, _ => hE
  | s :: l, j, hE, h => by
    change and (Nat.rec (motive := fun _ => Bool) (Nat.beq (getL S E j) (taut W))
        (fun s' _ => and (Nat.ble (Nat.succ s') n) (Nat.beq (getL S E j) (getL S D s'))) s)
      (selOK W S D n E l (Nat.succ j)) = true at h
    rw [Bool.and_eq_true] at h
    have hj : msat τ W (getL S E j) := by
      have h1 := h.1
      cases s with
      | zero =>
        have heq : getL S E j = taut W := Nat.eq_of_beq_eq_true h1
        rw [heq]; exact msat_taut hW
      | succ s' =>
        change and (Nat.ble (Nat.succ s') n) (Nat.beq (getL S E j) (getL S D s')) = true at h1
        rw [Bool.and_eq_true] at h1
        rw [Nat.eq_of_beq_eq_true h1.2]; exact hd s' (Nat.le_of_ble_eq_true h1.1)
    have := sel_sound hW hd l (Nat.succ j) (sat_succ hE hj) h.2
    rw [List.length_cons, show j + (l.length + 1) = Nat.succ j + l.length by omega]; exact this

theorem not_sat_zero {τ : Nat → Bool} {W S : Nat} {E : List Nat} {m k : Nat} (h : SatL τ W S E m)
    (hk : Nat.ble (Nat.succ k) m = true) (h0 : Nat.beq (getL S E k) 0 = true) : False := by
  have := h k (Nat.le_of_ble_eq_true hk)
  rw [Nat.eq_of_beq_eq_true h0] at this
  exact msat_zero this

theorem sat_get {τ : Nat → Bool} {W S : Nat} {E : List Nat} {m k : Nat} (h : SatL τ W S E m)
    (hk : Nat.ble (Nat.succ k) m = true) : msat τ W (getL S E k) :=
  h k (Nat.le_of_ble_eq_true hk)

end CRup
