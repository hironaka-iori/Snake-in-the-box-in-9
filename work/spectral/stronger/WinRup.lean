import WinCNF
/-!
# WinRup: kernel-friendly reverse-unit-propagation (RUP) steps on bitmask clauses

A clause is stored as a pair of bitmasks `(p, n)`: bit `v` of `p` (of `n`) is set when the
literal `v` (the literal `-v`) occurs.  `rup hs c = true` says: assuming the negation of `c`,
unit propagation through the hint clauses `hs` (in the given order) reaches a conflict.
`rup_sound` proves that this implies `c` under every assignment satisfying the hints.
-/
namespace WinRup
open WinCNF

abbrev Mask := Nat × Nat

/-- An assignment satisfies a bitmask clause. -/
def msat (τ : Nat → Bool) (m : Mask) : Prop :=
  ∃ v, (m.1.testBit v = true ∧ τ v = true) ∨ (m.2.testBit v = true ∧ τ v = false)

def litMask : Lit → Mask
  | .ofNat n => (2 ^ n, 0)
  | .negSucc n => (0, 2 ^ (n + 1))

def toMask : Clause → Mask
  | [] => (0, 0)
  | l :: c => (Nat.lor (litMask l).1 (toMask c).1, Nat.lor (litMask l).2 (toMask c).2)

theorem msat_toMask (τ : Nat → Bool) : ∀ c : Clause, clauseSat τ c → msat τ (toMask c)
  | [], h => by simp [clauseSat] at h
  | l :: c, h => by
    simp only [clauseSat, List.any_cons, Bool.or_eq_true] at h
    rcases h with h | h
    · cases l with
      | ofNat n =>
        refine ⟨n, Or.inl ⟨?_, h⟩⟩
        show (2 ^ n ||| (toMask c).1).testBit n = true
        simp [Nat.testBit_or, Nat.testBit_two_pow_self]
      | negSucc n =>
        simp only [litSat, Bool.not_eq_true'] at h
        refine ⟨n + 1, Or.inr ⟨?_, h⟩⟩
        show (2 ^ (n + 1) ||| (toMask c).2).testBit (n + 1) = true
        simp [Nat.testBit_or, Nat.testBit_two_pow_self]
    · obtain ⟨v, hv⟩ := msat_toMask τ c h
      refine ⟨v, ?_⟩
      show ((litMask l).1 ||| (toMask c).1).testBit v = true ∧ τ v = true ∨
        ((litMask l).2 ||| (toMask c).2).testBit v = true ∧ τ v = false
      simp only [Nat.testBit_or]
      rcases hv with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨by simp [h1], h2⟩
      · exact Or.inr ⟨by simp [h1], h2⟩

/-- All clauses of a list are satisfied (a right-nested conjunction). -/
def AllSat (τ : Nat → Bool) (l : List Mask) : Prop :=
  List.rec (motive := fun _ => Prop) True (fun m _ ih => msat τ m ∧ ih) l

theorem allSat_cons {τ : Nat → Bool} {m : Mask} {ms : List Mask} :
    AllSat τ (m :: ms) = (msat τ m ∧ AllSat τ ms) := rfl

theorem as_nil (τ : Nat → Bool) : AllSat τ [] := trivial
theorem as_cons (τ : Nat → Bool) (m : Mask) (ms : List Mask) (a : msat τ m) (b : AllSat τ ms) :
    AllSat τ (m :: ms) := ⟨a, b⟩

theorem allSat_map (τ : Nat → Bool) : ∀ l : List Clause,
    (∀ c ∈ l, clauseSat τ c) → AllSat τ (l.map toMask)
  | [], _ => trivial
  | c :: l, h => allSat_cons ▸ ⟨msat_toMask τ c (h c (List.mem_cons_self ..)),
      allSat_map τ l (fun d hd => h d (List.mem_cons_of_mem _ hd))⟩

theorem forall_append {P : Clause → Prop} {a b : List Clause} (h : ∀ c ∈ a ++ b, P c) :
    (∀ c ∈ a, P c) ∧ (∀ c ∈ b, P c) :=
  ⟨fun c hc => h c (List.mem_append_left _ hc), fun c hc => h c (List.mem_append_right _ hc)⟩

/-- Unit propagation with a direct `List.rec` (no `brecOn`), cheap for the kernel.
`tm`/`fm`: variables currently forced true/false.  For each hint, `rp`/`rn` are its positive
and negative literals not yet falsified; the hint must be falsified (`r = 0`, conflict) or
unit (`r` a single bit, and not a tautology on that bit). -/
noncomputable def go (l : List Mask) : Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => false)
    (fun h _ ih tm fm =>
      let rp := Nat.xor h.1 (Nat.land h.1 fm)
      let rn := Nat.xor h.2 (Nat.land h.2 tm)
      let r := Nat.lor rp rn
      Nat.beq r 0 || (Nat.beq (Nat.land r (r - 1)) 0 && Nat.beq (Nat.land rp rn) 0 &&
        ih (Nat.lor tm rp) (Nat.lor fm rn))) l

noncomputable def rup (hs : List Mask) (c : Mask) : Bool := go hs c.2 c.1

/-! ### Soundness -/

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

theorem single_bit {r a b : Nat} (h0 : Nat.land r (r - 1) = 0)
    (ha : r.testBit a = true) (hb : r.testBit b = true) : a = b := by
  have key : ∀ {a b : Nat}, a < b → r.testBit a = true → r.testBit b = true → False := by
    intro a b hab ha hb
    have h1 : (Nat.land r (r - 1)).testBit b = true := by
      show (r &&& (r - 1)).testBit b = true
      rw [Nat.testBit_and, testBit_pred_of_lt hab ha, hb]; rfl
    rw [h0, Nat.zero_testBit] at h1
    exact Bool.false_ne_true h1
  rcases Nat.lt_trichotomy a b with h | h | h
  · exact (key h ha hb).elim
  · exact h
  · exact (key h hb ha).elim

/-- `tm`/`fm` agree with `τ`. -/
def Cons (τ : Nat → Bool) (tm fm : Nat) : Prop :=
  ∀ v, (tm.testBit v = true → τ v = true) ∧ (fm.testBit v = true → τ v = false)

theorem go_sound (τ : Nat → Bool) : ∀ (hs : List Mask) (tm fm : Nat),
    AllSat τ hs → Cons τ tm fm → go hs tm fm = true → False
  | [], _, _, _, _, hg => Bool.false_ne_true hg
  | h :: hs, tm, fm, hall, hc, hg => by
    have hg' : (Nat.beq (Nat.lor (Nat.xor h.1 (Nat.land h.1 fm)) (Nat.xor h.2 (Nat.land h.2 tm))) 0 ||
        (Nat.beq (Nat.land (Nat.lor (Nat.xor h.1 (Nat.land h.1 fm)) (Nat.xor h.2 (Nat.land h.2 tm)))
          (Nat.lor (Nat.xor h.1 (Nat.land h.1 fm)) (Nat.xor h.2 (Nat.land h.2 tm)) - 1)) 0 &&
         Nat.beq (Nat.land (Nat.xor h.1 (Nat.land h.1 fm)) (Nat.xor h.2 (Nat.land h.2 tm))) 0 &&
         go hs (Nat.lor tm (Nat.xor h.1 (Nat.land h.1 fm)))
           (Nat.lor fm (Nat.xor h.2 (Nat.land h.2 tm))))) = true := hg
    generalize hrp : Nat.xor h.1 (Nat.land h.1 fm) = rp at hg'
    generalize hrn : Nat.xor h.2 (Nat.land h.2 tm) = rn at hg'
    have trp : ∀ v, rp.testBit v = (h.1.testBit v && !fm.testBit v) := by
      intro v; rw [← hrp]
      show (h.1 ^^^ (h.1 &&& fm)).testBit v = _
      rw [Nat.testBit_xor, Nat.testBit_and]
      cases h.1.testBit v <;> cases fm.testBit v <;> rfl
    have trn : ∀ v, rn.testBit v = (h.2.testBit v && !tm.testBit v) := by
      intro v; rw [← hrn]
      show (h.2 ^^^ (h.2 &&& tm)).testBit v = _
      rw [Nat.testBit_xor, Nat.testBit_and]
      cases h.2.testBit v <;> cases tm.testBit v <;> rfl
    have tor : ∀ x y v, (Nat.lor x y).testBit v = (x.testBit v || y.testBit v) :=
      fun x y v => Nat.testBit_or x y v
    have tand : ∀ x y v, (Nat.land x y).testBit v = (x.testBit v && y.testBit v) :=
      fun x y v => Nat.testBit_and x y v
    -- the hint is satisfied by a literal that is not yet falsified
    obtain ⟨v, hv⟩ : ∃ v, (rp.testBit v = true ∧ τ v = true) ∨ (rn.testBit v = true ∧ τ v = false) := by
      obtain ⟨v, hv⟩ := hall.1
      refine ⟨v, ?_⟩
      rcases hv with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · left; refine ⟨?_, h2⟩
        rw [trp, h1]
        cases hf : fm.testBit v
        · rfl
        · rw [(hc v).2 hf] at h2; exact absurd h2 (by decide)
      · right; refine ⟨?_, h2⟩
        rw [trn, h1]
        cases ht : tm.testBit v
        · rfl
        · rw [(hc v).1 ht] at h2; exact absurd h2 (by decide)
    have hrv : (Nat.lor rp rn).testBit v = true := by
      rw [tor]; rcases hv with ⟨h1, _⟩ | ⟨h1, _⟩ <;> simp [h1]
    have hr0 : Nat.beq (Nat.lor rp rn) 0 = false := by
      cases hb : Nat.beq (Nat.lor rp rn) 0
      · rfl
      · rw [Nat.eq_of_beq_eq_true hb, Nat.zero_testBit] at hrv; exact absurd hrv Bool.false_ne_true
    rw [hr0, Bool.false_or, Bool.and_eq_true, Bool.and_eq_true] at hg'
    obtain ⟨⟨hs1, hs2⟩, hrec⟩ := hg'
    have hs1 := Nat.eq_of_beq_eq_true hs1
    have hs2 := Nat.eq_of_beq_eq_true hs2
    -- every bit of rp or rn is the bit v
    have only : ∀ u, (rp.testBit u = true ∨ rn.testBit u = true) → u = v := by
      intro u hu
      apply single_bit hs1 _ hrv
      rw [tor]; rcases hu with h1 | h1 <;> simp [h1]
    have notboth : ∀ u, rp.testBit u = true → rn.testBit u = true → False := by
      intro u h1 h2
      have : (Nat.land rp rn).testBit u = true := by rw [tand, h1, h2]; rfl
      rw [hs2, Nat.zero_testBit] at this; exact Bool.false_ne_true this
    apply go_sound τ hs _ _ hall.2 _ hrec
    intro u
    constructor
    · intro hu
      rw [tor] at hu
      rcases Bool.or_eq_true _ _ ▸ hu with hu | hu
      · exact (hc u).1 hu
      · have := only u (Or.inl hu); subst this
        rcases hv with ⟨_, h2⟩ | ⟨h1, _⟩
        · exact h2
        · exact (notboth u hu h1).elim
    · intro hu
      rw [tor] at hu
      rcases Bool.or_eq_true _ _ ▸ hu with hu | hu
      · exact (hc u).2 hu
      · have := only u (Or.inr hu); subst this
        rcases hv with ⟨h1, _⟩ | ⟨_, h2⟩
        · exact (notboth u h1 hu).elim
        · exact h2

theorem rup_sound {τ : Nat → Bool} {hs : List Mask} {c : Mask} (hr : rup hs c = true)
    (hh : AllSat τ hs) : msat τ c := by
  apply Classical.byContradiction
  intro hn
  apply go_sound τ hs c.2 c.1 hh _ hr
  intro v
  constructor
  · intro hv
    cases ht : τ v
    · exact (hn ⟨v, Or.inr ⟨hv, ht⟩⟩).elim
    · rfl
  · intro hv
    cases ht : τ v
    · rfl
    · exact (hn ⟨v, Or.inl ⟨hv, ht⟩⟩).elim

theorem msat_empty {τ : Nat → Bool} : ¬ msat τ (0, 0) := by
  intro ⟨v, hv⟩
  simp [Nat.zero_testBit] at hv

end WinRup
