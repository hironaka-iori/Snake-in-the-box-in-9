import SymPit
/-! Glue, part 1: subcube counts, their transport along generators, and moving a largest 6-subcube to
copy 0 of coordinates (6,7). -/
set_option linter.deprecated false
set_option maxRecDepth 200000
namespace Dim8Lift.Sym
open Dim8Lift Dim8Lift.Cube

def fl (c j : Nat) : Bool := decide (28 ≤ c ∧ j = c - 28)

theorem gen_bit_0 : ∀ u : Fin 256, ∀ j : Fin 8, (gen 0 u.val).testBit j.val = (u.val.testBit (dmap 0 j.val) != fl 0 j.val) := by decide
theorem gen_bit_1 : ∀ u : Fin 256, ∀ j : Fin 8, (gen 1 u.val).testBit j.val = (u.val.testBit (dmap 1 j.val) != fl 1 j.val) := by decide
theorem gen_bit_2 : ∀ u : Fin 256, ∀ j : Fin 8, (gen 2 u.val).testBit j.val = (u.val.testBit (dmap 2 j.val) != fl 2 j.val) := by decide
theorem gen_bit_3 : ∀ u : Fin 256, ∀ j : Fin 8, (gen 3 u.val).testBit j.val = (u.val.testBit (dmap 3 j.val) != fl 3 j.val) := by decide
theorem gen_bit_4 : ∀ u : Fin 256, ∀ j : Fin 8, (gen 4 u.val).testBit j.val = (u.val.testBit (dmap 4 j.val) != fl 4 j.val) := by decide
theorem gen_bit_5 : ∀ u : Fin 256, ∀ j : Fin 8, (gen 5 u.val).testBit j.val = (u.val.testBit (dmap 5 j.val) != fl 5 j.val) := by decide
theorem gen_bit_6 : ∀ u : Fin 256, ∀ j : Fin 8, (gen 6 u.val).testBit j.val = (u.val.testBit (dmap 6 j.val) != fl 6 j.val) := by decide
theorem gen_bit_7 : ∀ u : Fin 256, ∀ j : Fin 8, (gen 7 u.val).testBit j.val = (u.val.testBit (dmap 7 j.val) != fl 7 j.val) := by decide
theorem gen_bit_8 : ∀ u : Fin 256, ∀ j : Fin 8, (gen 8 u.val).testBit j.val = (u.val.testBit (dmap 8 j.val) != fl 8 j.val) := by decide
theorem gen_bit_9 : ∀ u : Fin 256, ∀ j : Fin 8, (gen 9 u.val).testBit j.val = (u.val.testBit (dmap 9 j.val) != fl 9 j.val) := by decide
theorem gen_bit_10 : ∀ u : Fin 256, ∀ j : Fin 8, (gen 10 u.val).testBit j.val = (u.val.testBit (dmap 10 j.val) != fl 10 j.val) := by decide
theorem gen_bit_11 : ∀ u : Fin 256, ∀ j : Fin 8, (gen 11 u.val).testBit j.val = (u.val.testBit (dmap 11 j.val) != fl 11 j.val) := by decide
theorem gen_bit_12 : ∀ u : Fin 256, ∀ j : Fin 8, (gen 12 u.val).testBit j.val = (u.val.testBit (dmap 12 j.val) != fl 12 j.val) := by decide
theorem gen_bit_13 : ∀ u : Fin 256, ∀ j : Fin 8, (gen 13 u.val).testBit j.val = (u.val.testBit (dmap 13 j.val) != fl 13 j.val) := by decide
theorem gen_bit_14 : ∀ u : Fin 256, ∀ j : Fin 8, (gen 14 u.val).testBit j.val = (u.val.testBit (dmap 14 j.val) != fl 14 j.val) := by decide
theorem gen_bit_15 : ∀ u : Fin 256, ∀ j : Fin 8, (gen 15 u.val).testBit j.val = (u.val.testBit (dmap 15 j.val) != fl 15 j.val) := by decide
theorem gen_bit_16 : ∀ u : Fin 256, ∀ j : Fin 8, (gen 16 u.val).testBit j.val = (u.val.testBit (dmap 16 j.val) != fl 16 j.val) := by decide
theorem gen_bit_17 : ∀ u : Fin 256, ∀ j : Fin 8, (gen 17 u.val).testBit j.val = (u.val.testBit (dmap 17 j.val) != fl 17 j.val) := by decide
theorem gen_bit_18 : ∀ u : Fin 256, ∀ j : Fin 8, (gen 18 u.val).testBit j.val = (u.val.testBit (dmap 18 j.val) != fl 18 j.val) := by decide
theorem gen_bit_19 : ∀ u : Fin 256, ∀ j : Fin 8, (gen 19 u.val).testBit j.val = (u.val.testBit (dmap 19 j.val) != fl 19 j.val) := by decide
theorem gen_bit_20 : ∀ u : Fin 256, ∀ j : Fin 8, (gen 20 u.val).testBit j.val = (u.val.testBit (dmap 20 j.val) != fl 20 j.val) := by decide
theorem gen_bit_21 : ∀ u : Fin 256, ∀ j : Fin 8, (gen 21 u.val).testBit j.val = (u.val.testBit (dmap 21 j.val) != fl 21 j.val) := by decide
theorem gen_bit_22 : ∀ u : Fin 256, ∀ j : Fin 8, (gen 22 u.val).testBit j.val = (u.val.testBit (dmap 22 j.val) != fl 22 j.val) := by decide
theorem gen_bit_23 : ∀ u : Fin 256, ∀ j : Fin 8, (gen 23 u.val).testBit j.val = (u.val.testBit (dmap 23 j.val) != fl 23 j.val) := by decide
theorem gen_bit_24 : ∀ u : Fin 256, ∀ j : Fin 8, (gen 24 u.val).testBit j.val = (u.val.testBit (dmap 24 j.val) != fl 24 j.val) := by decide
theorem gen_bit_25 : ∀ u : Fin 256, ∀ j : Fin 8, (gen 25 u.val).testBit j.val = (u.val.testBit (dmap 25 j.val) != fl 25 j.val) := by decide
theorem gen_bit_26 : ∀ u : Fin 256, ∀ j : Fin 8, (gen 26 u.val).testBit j.val = (u.val.testBit (dmap 26 j.val) != fl 26 j.val) := by decide
theorem gen_bit_27 : ∀ u : Fin 256, ∀ j : Fin 8, (gen 27 u.val).testBit j.val = (u.val.testBit (dmap 27 j.val) != fl 27 j.val) := by decide
theorem gen_bit_28 : ∀ u : Fin 256, ∀ j : Fin 8, (gen 28 u.val).testBit j.val = (u.val.testBit (dmap 28 j.val) != fl 28 j.val) := by decide
theorem gen_bit_29 : ∀ u : Fin 256, ∀ j : Fin 8, (gen 29 u.val).testBit j.val = (u.val.testBit (dmap 29 j.val) != fl 29 j.val) := by decide
theorem gen_bit_30 : ∀ u : Fin 256, ∀ j : Fin 8, (gen 30 u.val).testBit j.val = (u.val.testBit (dmap 30 j.val) != fl 30 j.val) := by decide
theorem gen_bit_31 : ∀ u : Fin 256, ∀ j : Fin 8, (gen 31 u.val).testBit j.val = (u.val.testBit (dmap 31 j.val) != fl 31 j.val) := by decide
theorem gen_bit_32 : ∀ u : Fin 256, ∀ j : Fin 8, (gen 32 u.val).testBit j.val = (u.val.testBit (dmap 32 j.val) != fl 32 j.val) := by decide
theorem gen_bit_33 : ∀ u : Fin 256, ∀ j : Fin 8, (gen 33 u.val).testBit j.val = (u.val.testBit (dmap 33 j.val) != fl 33 j.val) := by decide
theorem gen_bit_34 : ∀ u : Fin 256, ∀ j : Fin 8, (gen 34 u.val).testBit j.val = (u.val.testBit (dmap 34 j.val) != fl 34 j.val) := by decide
theorem gen_bit_35 : ∀ u : Fin 256, ∀ j : Fin 8, (gen 35 u.val).testBit j.val = (u.val.testBit (dmap 35 j.val) != fl 35 j.val) := by decide
theorem gen_bit_F : ∀ c : Fin 36, ∀ u : Fin 256, ∀ j : Fin 8,
    (gen c.val u.val).testBit j.val = (u.val.testBit (dmap c.val j.val) != fl c.val j.val)
  | ⟨0, _⟩ => gen_bit_0
  | ⟨1, _⟩ => gen_bit_1
  | ⟨2, _⟩ => gen_bit_2
  | ⟨3, _⟩ => gen_bit_3
  | ⟨4, _⟩ => gen_bit_4
  | ⟨5, _⟩ => gen_bit_5
  | ⟨6, _⟩ => gen_bit_6
  | ⟨7, _⟩ => gen_bit_7
  | ⟨8, _⟩ => gen_bit_8
  | ⟨9, _⟩ => gen_bit_9
  | ⟨10, _⟩ => gen_bit_10
  | ⟨11, _⟩ => gen_bit_11
  | ⟨12, _⟩ => gen_bit_12
  | ⟨13, _⟩ => gen_bit_13
  | ⟨14, _⟩ => gen_bit_14
  | ⟨15, _⟩ => gen_bit_15
  | ⟨16, _⟩ => gen_bit_16
  | ⟨17, _⟩ => gen_bit_17
  | ⟨18, _⟩ => gen_bit_18
  | ⟨19, _⟩ => gen_bit_19
  | ⟨20, _⟩ => gen_bit_20
  | ⟨21, _⟩ => gen_bit_21
  | ⟨22, _⟩ => gen_bit_22
  | ⟨23, _⟩ => gen_bit_23
  | ⟨24, _⟩ => gen_bit_24
  | ⟨25, _⟩ => gen_bit_25
  | ⟨26, _⟩ => gen_bit_26
  | ⟨27, _⟩ => gen_bit_27
  | ⟨28, _⟩ => gen_bit_28
  | ⟨29, _⟩ => gen_bit_29
  | ⟨30, _⟩ => gen_bit_30
  | ⟨31, _⟩ => gen_bit_31
  | ⟨32, _⟩ => gen_bit_32
  | ⟨33, _⟩ => gen_bit_33
  | ⟨34, _⟩ => gen_bit_34
  | ⟨35, _⟩ => gen_bit_35
  | ⟨n + 36, h⟩ => absurd h (by omega)

theorem gen_bit {c u j : Nat} (hc : c < 36) (hu : u < 256) (hj : j < 8) :
    (gen c u).testBit j = (u.testBit (dmap c j) != fl c j) := gen_bit_F ⟨c, hc⟩ ⟨u, hu⟩ ⟨j, hj⟩

def inSub (a b : Nat) (va vb : Bool) (u : Nat) : Bool := (u.testBit a == va) && (u.testBit b == vb)
def cntSub (S : Nat → Bool) (a b : Nat) (va vb : Bool) : Nat := cnt 256 (fun u => S u && inSub a b va vb u)

/-- every 6-subcube holds at most k vertices of S -/
@[irreducible] def MaxSub (S : Nat → Bool) (k : Nat) : Prop :=
  ∀ a b, a < 8 → b < 8 → a ≠ b → ∀ va vb, cntSub S a b va vb ≤ k

theorem cnt_perm {c : Nat} (hc : c < 36) (p : Nat → Bool) :
    cnt 256 (fun u => p (gen c u)) = cnt 256 p := by
  unfold cnt; exact sm_perm hc (fun u => if p u then 1 else 0)

theorem bxor_beq (x va f : Bool) : ((x != f) == (va != f)) = (x == va) := by
  cases x <;> cases va <;> cases f <;> rfl

theorem maxSub_gen {c : Nat} (hc : c < 36) {S : Nat → Bool} {k : Nat} (h : MaxSub S k) :
    MaxSub (fun u => S (gen c u)) k := by
  unfold MaxSub at h ⊢
  intro a b ha hb hab va vb
  unfold cntSub
  have e : cnt 256 (fun u => S (gen c u) && inSub a b va vb u) =
      cnt 256 (fun v => S v && inSub (dmap c a) (dmap c b) (va != fl c a) (vb != fl c b) v) := by
    rw [← cnt_perm hc (fun v => S v && inSub (dmap c a) (dmap c b) (va != fl c a) (vb != fl c b) v)]
    unfold cnt; apply sm_congr; intro u hu
    have e1 : (gen c u).testBit (dmap c a) = (u.testBit (dmap c (dmap c a)) != fl c (dmap c a)) := gen_bit hc hu (dmap_lt hc ha)
    rw [dmap_dmap hc ha] at e1
    have e2 : (gen c u).testBit (dmap c b) = (u.testBit (dmap c (dmap c b)) != fl c (dmap c b)) := gen_bit hc hu (dmap_lt hc hb)
    rw [dmap_dmap hc hb] at e2
    have f1 : ∀ x, x < 8 → fl c (dmap c x) = fl c x := by
      intro x hx
      by_cases h28 : c < 28
      · have : ¬ 28 ≤ c := by omega
        simp [fl, this]
      · unfold dmap; rw [if_neg h28]
    rw [f1 a ha] at e1; rw [f1 b hb] at e2
    show (if (S (gen c u) && inSub a b va vb u) = true then 1 else 0) =
      (if (S (gen c u) && inSub (dmap c a) (dmap c b) (va != fl c a) (vb != fl c b) (gen c u)) = true then 1 else 0)
    unfold inSub; rw [e1, e2, bxor_beq (u.testBit a), bxor_beq (u.testBit b)]
  rw [e]
  have inj : dmap c a ≠ dmap c b := by
    intro e; have := congrArg (dmap c) e; rw [dmap_dmap hc ha, dmap_dmap hc hb] at this; exact hab this
  exact h _ _ (dmap_lt hc ha) (dmap_lt hc hb) inj _ _

def applyW : List Nat → Nat → Nat
  | [], u => u
  | c :: w, u => gen c (applyW w u)

theorem applyW_lt : ∀ (w : List Nat), (∀ c ∈ w, c < 36) → ∀ u, u < 256 → applyW w u < 256
  | [], _, u, hu => hu
  | c :: w, hw, u, hu => gen_lt (hw c (by simp)) (applyW_lt w (fun c' h => hw c' (by simp [h])) u hu)

theorem pit_word {c' L D : Nat} : ∀ (w : List Nat), (∀ c ∈ w, c < 36) → ∀ {S : Nat → Bool} {ℓ : Nat → Nat},
    Pit c' L D S ℓ → Pit c' L D (fun u => S (applyW w u)) (fun u => ℓ (applyW w u))
  | [], _, _, _, h => h
  | c :: w, hw, S, ℓ, h => by
    have e1 : (fun u => S (applyW (c :: w) u)) = (fun u => (fun v => S (gen c v)) (applyW w u)) := by
      funext u; rfl
    have e2 : (fun u => ℓ (applyW (c :: w) u)) = (fun u => (fun v => ℓ (gen c v)) (applyW w u)) := by
      funext u; rfl
    rw [e1, e2]
    exact pit_word w (fun c' h' => hw c' (by simp [h'])) (pit_gen (hw c (by simp)) h)

theorem maxSub_word : ∀ (w : List Nat), (∀ c ∈ w, c < 36) → ∀ {S : Nat → Bool} {k : Nat},
    MaxSub S k → MaxSub (fun u => S (applyW w u)) k
  | [], _, _, _, h => h
  | c :: w, hw, S, k, h => by
    have e1 : (fun u => S (applyW (c :: w) u)) = (fun u => (fun v => S (gen c v)) (applyW w u)) := by
      funext u; rfl
    rw [e1]
    have h1 : MaxSub (fun v => S (gen c v)) k := maxSub_gen (hw c (by simp)) h
    exact maxSub_word w (fun c' h' => hw c' (by simp [h'])) (S := fun v => S (gen c v)) (k := k) h1

end Dim8Lift.Sym
