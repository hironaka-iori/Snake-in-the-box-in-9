import WinCNF
/-!
# FastRup: a non-recursive, single-`Nat` RUP step for kernel evaluation

Literal positions with stride `W` (every variable `< W`): bit `64 + v` is the literal `v`, bit
`64 + W + v` the literal `-v`.  Bits `0..63` are always-false padding; the generator fills them
with a per-clause tag so that kernel hashes of mask literals (their low 64 bits) are distinct.
A clause is one `Nat` (the set of its literal positions).

A RUP step is checked as an explicit chain of states `F₀ = C ||| pad`, `Fᵢ = stepF W Fᵢ₋₁ cᵢ`
(each state is the set of literal positions known to be false), closed by `finF W Fₘ₋₁ cₘ = true`.
`stepF` is not recursive and uses only kernel-accelerated `Nat` operations
(`xor`, `land`, `sub`, `beq`, `lor`, `shiftLeft`, `shiftRight`), so the kernel evaluates a hint
in a handful of reductions.  The soundness lemmas `start`, `step_sound`, `close` are ordinary
theorems; the proof of a step is a chain of their applications whose only computation is the
closing `Eq.refl true`.
-/
namespace FastRup
open WinCNF

/-- Truth value of the literal at position `x`. -/
def litT (τ : Nat → Bool) (W x : Nat) : Bool :=
  if x < 64 then false else if x < 64 + W then τ (x - 64)
  else if x < 64 + W + W then !τ (x - 64 - W) else false

/-- The padding bits, assumed false at the start of every step. -/
def pad : Nat := 18446744073709551615

/-- `τ` satisfies the clause `c`. -/
def msat (τ : Nat → Bool) (W c : Nat) : Prop := ∃ x, c.testBit x = true ∧ litT τ W x = true

/-- Every literal position in `F` is false under `τ`. -/
def Inv (τ : Nat → Bool) (W F : Nat) : Prop := ∀ x, F.testBit x = true → litT τ W x = false

/-- One unit-propagation step: `r` = literals of `c` not yet false; if `r` has at most one bit,
mark its complement false (positions `x ± W`; the out-of-range one is harmless). -/
noncomputable def stepF (W F c : Nat) : Nat :=
  let r := Nat.xor c (Nat.land c F)
  Bool.rec (motive := fun _ => Nat) F
    (Nat.lor F (Nat.lor (Nat.shiftLeft r W) (Nat.shiftRight r W)))
    (Nat.beq (Nat.land r (Nat.sub r (nat_lit 1))) (nat_lit 0))

/-- Conflict: every literal of `c` is false. -/
def finF (_W F c : Nat) : Bool := Nat.beq (Nat.xor c (Nat.land c F)) (nat_lit 0)

/-! ### Bit lemmas -/

theorem testBit_pred_of_lt {r a b : Nat} (hab : a < b) (ha : r.testBit a = true) :
    (r - 1).testBit b = r.testBit b := by
  have hpos : 0 < 2 ^ b := Nat.two_pow_pos b
  have hm : r % 2 ^ b ≠ 0 := by
    intro h0
    have h1 := Nat.testBit_mod_two_pow r b a
    rw [h0, Nat.zero_testBit] at h1
    simp [hab, ha] at h1
  have hlt := Nat.mod_lt r hpos
  have hd := Nat.div_add_mod r (2 ^ b)
  have hq : (r - 1) / 2 ^ b = r / 2 ^ b := by
    generalize r / 2 ^ b = q at hd ⊢
    generalize r % 2 ^ b = m at hd hm hlt
    generalize hk : 2 ^ b * q = k at hd
    have e : r - 1 = k + (m - 1) := by omega
    rw [e, ← hk, Nat.mul_add_div hpos, Nat.div_eq_of_lt (by omega), Nat.add_zero]
  rw [Nat.testBit_to_div_mod, Nat.testBit_to_div_mod (x := r), hq]

theorem single_bit {r a b : Nat} (h0 : Nat.land r (Nat.sub r 1) = 0)
    (ha : r.testBit a = true) (hb : r.testBit b = true) : a = b := by
  have key : ∀ {a b : Nat}, a < b → r.testBit a = true → r.testBit b = true → False := by
    intro a b hab ha hb
    have h1 : (Nat.land r (Nat.sub r 1)).testBit b = true := by
      show (r &&& (r - 1)).testBit b = true
      rw [Nat.testBit_and, testBit_pred_of_lt hab ha, hb]; rfl
    rw [h0, Nat.zero_testBit] at h1
    exact Bool.false_ne_true h1
  rcases Nat.lt_trichotomy a b with h | h | h
  · exact (key h ha hb).elim
  · exact h
  · exact (key h hb ha).elim

theorem tb_xor_and (c F x : Nat) :
    (Nat.xor c (Nat.land c F)).testBit x = (c.testBit x && !F.testBit x) := by
  show (c ^^^ (c &&& F)).testBit x = _
  rw [Nat.testBit_xor, Nat.testBit_and]
  cases c.testBit x <;> cases F.testBit x <;> rfl

/-! ### Soundness -/

theorem testBit_pad {x : Nat} (h : pad.testBit x = true) : x < 64 := by
  have : pad = 2 ^ 64 - 1 := rfl
  rw [this, Nat.testBit_two_pow_sub_one] at h
  exact of_decide_eq_true h

theorem start {τ : Nat → Bool} {W C : Nat} (hn : ¬ msat τ W C) : Inv τ W (Nat.lor C pad) := by
  intro x hx
  change (C ||| pad).testBit x = true at hx
  rw [Nat.testBit_or] at hx
  rcases Bool.or_eq_true _ _ ▸ hx with hx | hx
  · cases h : litT τ W x
    · rfl
    · exact absurd ⟨x, hx, h⟩ hn
  · have := testBit_pad hx
    simp [litT, this]

theorem not_false_of_true {τ : Nat → Bool} {W F c : Nat} (hc : msat τ W c) (hF : Inv τ W F) :
    ∃ x, (Nat.xor c (Nat.land c F)).testBit x = true ∧ litT τ W x = true := by
  obtain ⟨x, hx, hl⟩ := hc
  refine ⟨x, ?_, hl⟩
  rw [tb_xor_and, hx]
  cases hf : F.testBit x
  · rfl
  · rw [hF x hf] at hl; exact absurd hl Bool.false_ne_true

theorem litT_cases {τ : Nat → Bool} {W x : Nat} (h : litT τ W x = true) :
    (64 ≤ x ∧ x < 64 + W ∧ τ (x - 64) = true) ∨
    (64 + W ≤ x ∧ x < 64 + W + W ∧ τ (x - 64 - W) = false) := by
  unfold litT at h
  by_cases h1 : x < 64
  · rw [if_pos h1] at h; exact absurd h Bool.false_ne_true
  rw [if_neg h1] at h
  by_cases h2 : x < 64 + W
  · rw [if_pos h2] at h; exact Or.inl ⟨by omega, h2, h⟩
  rw [if_neg h2] at h
  by_cases h3 : x < 64 + W + W
  · rw [if_pos h3] at h
    refine Or.inr ⟨by omega, h3, ?_⟩
    cases e : τ (x - 64 - W)
    · rfl
    · rw [e] at h; exact absurd h Bool.false_ne_true
  · rw [if_neg h3] at h; exact absurd h Bool.false_ne_true

theorem litT_up {τ : Nat → Bool} {W x : Nat} (h : litT τ W x = true) : litT τ W (x + W) = false := by
  unfold litT
  rcases litT_cases h with ⟨a, b, c⟩ | ⟨a, b, _⟩
  · rw [if_neg (by omega), if_neg (by omega), if_pos (by omega),
      show x + W - 64 - W = x - 64 by omega, c]; rfl
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]

theorem litT_down {τ : Nat → Bool} {W x y : Nat} (h : litT τ W x = true) (e : W + y = x) :
    litT τ W y = false := by
  unfold litT
  rcases litT_cases h with ⟨a, b, _⟩ | ⟨a, b, c⟩
  · rw [if_pos (by omega)]
  · rw [if_neg (by omega), if_pos (by omega), show y - 64 = x - 64 - W by omega, c]

theorem step_sound {τ : Nat → Bool} {W F c : Nat} (hc : msat τ W c) (hF : Inv τ W F) :
    Inv τ W (stepF W F c) := by
  obtain ⟨x, hrx, hlx⟩ := not_false_of_true hc hF
  unfold stepF
  generalize Nat.xor c (Nat.land c F) = r at hrx ⊢
  show Inv τ W (Bool.rec (motive := fun _ => Nat) F
    (Nat.lor F (Nat.lor (Nat.shiftLeft r W) (Nat.shiftRight r W))) (Nat.beq (Nat.land r (Nat.sub r 1)) 0))
  cases hb : Nat.beq (Nat.land r (Nat.sub r 1)) 0
  · exact hF
  · have h0 := Nat.eq_of_beq_eq_true hb
    have only : ∀ y, r.testBit y = true → y = x := fun y hy => single_bit h0 hy hrx
    intro y hy
    change (F ||| ((r <<< W) ||| (r >>> W))).testBit y = true at hy
    rw [Nat.testBit_or, Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_shiftRight] at hy
    rcases Bool.or_eq_true _ _ ▸ hy with hy | hy
    · exact hF y hy
    rcases Bool.or_eq_true _ _ ▸ hy with hy | hy
    · rw [Bool.and_eq_true, decide_eq_true_iff] at hy
      have e := only _ hy.2
      have : y = x + W := by omega
      subst this
      exact litT_up hlx
    · exact litT_down hlx (only _ hy)

theorem close {τ : Nat → Bool} {W F c : Nat} (hc : msat τ W c) (hF : Inv τ W F)
    (h : finF W F c = true) : False := by
  obtain ⟨x, hrx, _⟩ := not_false_of_true hc hF
  have h0 := Nat.eq_of_beq_eq_true h
  rw [h0, Nat.zero_testBit] at hrx
  exact Bool.false_ne_true hrx

/-- The proof of one RUP step: `rup τ W C (fun hn => close hₘ (step_sound hₘ₋₁ (… (start hn))) rfl)`. -/
theorem rup {τ : Nat → Bool} {W C : Nat} (h : ¬ msat τ W C → False) : msat τ W C :=
  Classical.byContradiction h

theorem msat_zero {τ : Nat → Bool} {W : Nat} : ¬ msat τ W 0 := by
  intro ⟨x, hx, _⟩
  rw [Nat.zero_testBit] at hx; exact Bool.false_ne_true hx

theorem msat_lor {τ : Nat → Bool} {W m t : Nat} (h : msat τ W m) : msat τ W (Nat.lor m t) := by
  obtain ⟨x, hx, hl⟩ := h
  exact ⟨x, by show (m ||| t).testBit x = true; rw [Nat.testBit_or, hx]; rfl, hl⟩

/-! ### Renamed input clauses

The proof works with compressed variable indices `v'`; `ren T B v'` reads the original variable
from the `B`-bit table `T`, and clause facts are about `rtau τ T B = τ ∘ ren T B`. -/

/-- Entry `v` of the packed `B`-bit table `T`. -/
def ren (T B v : Nat) : Nat := Nat.land (Nat.shiftRight T (Nat.mul v B)) (Nat.sub (Nat.shiftLeft 1 B) 1)

/-- The assignment seen through the renaming. -/
def rtau (τ : Nat → Bool) (T B : Nat) : Nat → Bool := fun v => τ (ren T B v)

/-- Position of literal `l` renamed to variable `v'` (checked against the table). -/
def litPosR (W T B : Nat) (l : Lit) (v' : Nat) : Option Nat :=
  match l with
  | .ofNat n => if v' < W ∧ ren T B v' = n then some (64 + v') else none
  | .negSucc n => if v' < W ∧ ren T B v' = n + 1 then some (64 + W + v') else none

/-- Mask of clause `c` with its literals renamed to `vs` (`none` on any mismatch). -/
def toMaskR (W T B : Nat) : Clause → List Nat → Option Nat
  | [], _ => some 0
  | _ :: _, [] => none
  | l :: c, v :: vs => match litPosR W T B l v, toMaskR W T B c vs with
    | some x, some m => some (Nat.lor (Nat.shiftLeft 1 x) m)
    | _, _ => none

theorem litT_litPosR {τ : Nat → Bool} {W T B : Nat} {l : Lit} {v x : Nat}
    (h : litPosR W T B l v = some x) (hl : litSat τ l = true) : litT (rtau τ T B) W x = true := by
  cases l with
  | ofNat n =>
    simp only [litPosR] at h
    split at h
    · rename_i hc
      cases h
      unfold litT
      rw [if_neg (by omega), if_pos (by omega), show 64 + v - 64 = v by omega]
      show τ (ren T B v) = true
      rw [hc.2]; exact hl
    · cases h
  | negSucc n =>
    simp only [litPosR] at h
    split at h
    · rename_i hc
      cases h
      unfold litT
      rw [if_neg (by omega), if_neg (by omega), if_pos (by omega),
        show 64 + W + v - 64 - W = v by omega]
      show (!τ (ren T B v)) = true
      rw [hc.2]; exact hl
    · cases h

theorem msat_toMaskR {τ : Nat → Bool} {W T B : Nat} :
    ∀ {c : Clause} {vs : List Nat} {m : Nat}, toMaskR W T B c vs = some m → clauseSat τ c →
      msat (rtau τ T B) W m
  | [], _, _, _, h => by simp [clauseSat] at h
  | _ :: _, [], _, hm, _ => by simp [toMaskR] at hm
  | l :: c, v :: vs, m, hm, h => by
    simp only [toMaskR] at hm
    split at hm
    · rename_i x m' hx hm'
      cases hm
      simp only [clauseSat, List.any_cons, Bool.or_eq_true] at h
      rcases h with h | h
      · exact ⟨x, by show (1 <<< x ||| m').testBit x = true; simp [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow_self],
          litT_litPosR hx h⟩
      · obtain ⟨y, hy, hl⟩ := msat_toMaskR hm' h
        exact ⟨y, by show (1 <<< x ||| m').testBit y = true; simp [Nat.testBit_or, hy], hl⟩
    · cases hm

end FastRup
