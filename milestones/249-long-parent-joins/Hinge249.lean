import LayerJoining

namespace Hinge249
open LayerJoining

variable {V : Type} {R : V → V → Prop}

/-- Only indices 0 through m of the projected word are used. -/
def SimpleWord (w : Nat → V) (m : Nat) : Prop :=
  ∀ i j, i ≤ m → j ≤ m → w i = w j → i = j

def Steps (R : V → V → Prop) (w : Nat → V) (m : Nat) : Prop :=
  ∀ i, i < m → R (w i) (w (i + 1))

/-- Duplicate the vertex at the cut, changing its binary layer. -/
def lifted (w : Nat → V) (k i : Nat) : V × Bool :=
  if i ≤ k then (w i, false) else (w (i - 1), true)

def Realizes (R : V → V → Prop) (w : Nat → V) (m k : Nat) : Prop :=
  ∃ p : InducedPath (V × Bool) (LayerAdj R) (m + 1),
    ∀ i, p.vertex i = lifted w k i.val

def Straddled (R : V → V → Prop) (w : Nat → V) (m k : Nat) : Prop :=
  ∀ i j, i + 1 < j → j ≤ m → R (w i) (w j) → i < k ∧ k < j

private def OnArms (R : V → V → Prop) (w : Nat → V) (m k : Nat) : Prop :=
  ∀ i j, i < j → j ≤ m → (j ≤ k ∨ k ≤ i) → (R (w i) (w j) ↔ i + 1 = j)

private def LayerPairs (R : V → V → Prop) (w : Nat → V) (m k : Nat) : Prop :=
  ∀ i j, i < j → j ≤ m + 1 → (LayerAdj R (lifted w k i) (lifted w k j) ↔ i + 1 = j)

private theorem arms_iff {w : Nat → V} {m k : Nat} (step : Steps R w m) :
    OnArms R w m k ↔ Straddled R w m k := by
  constructor
  · intro h i j gap hj adj
    by_cases hleft : j ≤ k
    · have e := (h i j (by omega) hj (Or.inl hleft)).mp adj
      omega
    by_cases hright : k ≤ i
    · have e := (h i j (by omega) hj (Or.inr hright)).mp adj
      omega
    omega
  · intro h i j hij hj side
    constructor
    · intro adj
      by_cases e : i + 1 = j
      · exact e
      · have cross := h i j (by omega) hj adj
        omega
    · intro e
      subst j
      exact step i (by omega)

private theorem lifted_distinct {w : Nat → V} {m k : Nat}
    (hk : k ≤ m) (simple : SimpleWord w m) (i j : Nat)
    (hi : i ≤ m + 1) (hj : j ≤ m + 1) (eq : lifted w k i = lifted w k j) : i = j := by
  by_cases a : i ≤ k <;> by_cases b : j ≤ k
  · have he : w i = w j := by simpa [lifted, a, b] using congrArg Prod.fst eq
    exact simple i j (by omega) (by omega) he
  · have he := congrArg Prod.snd eq
    simp [lifted, a, b] at he
  · have he := congrArg Prod.snd eq
    simp [lifted, a, b] at he
  · have he : w (i - 1) = w (j - 1) := by simpa [lifted, a, b] using congrArg Prod.fst eq
    have same := simple (i - 1) (j - 1) (by omega) (by omega) he
    omega

private theorem pairs_iff {w : Nat → V} {m k : Nat} (hk : k ≤ m) (simple : SimpleWord w m) :
    LayerPairs R w m k ↔ OnArms R w m k := by
  constructor
  · intro h i j hij hj side
    rcases side with before | after
    · have hi : i ≤ k := by omega
      simpa [lifted, hi, before, LayerAdj] using h i j hij (by omega)
    · have hi : ¬ i + 1 ≤ k := by omega
      have hj' : ¬ j + 1 ≤ k := by omega
      simpa [lifted, hi, hj', LayerAdj] using h (i + 1) (j + 1) (by omega) (by omega)
  · intro h i j hij hj
    by_cases b : j ≤ k
    · have a : i ≤ k := by omega
      simpa [lifted, a, b, LayerAdj] using h i j hij (by omega) (Or.inl b)
    · by_cases a : i ≤ k
      · simp only [lifted, if_pos a, if_neg b, LayerAdj, Bool.false_eq_true, false_and,
          ne_eq, not_false_eq_true, true_and, false_or]
        constructor
        · intro eq
          have t := simple i (j - 1) (by omega) (by omega) eq
          omega
        · intro e
          have t : j - 1 = i := by omega
          rw [t]
      · have sides := h (i - 1) (j - 1) (by omega) (by omega) (Or.inr (by omega))
        have shift : ((i - 1) + 1 = j - 1) ↔ i + 1 = j := by omega
        simpa [lifted, a, b, LayerAdj] using sides.trans shift

private theorem realizes_iff_pairs {w : Nat → V} {m k : Nat}
    (hk : k ≤ m) (simple : SimpleWord w m) :
    Realizes R w m k ↔ LayerPairs R w m k := by
  constructor
  · rintro ⟨p, hp⟩ i j hij hj
    have t := p.induced ⟨i, by omega⟩ ⟨j, by omega⟩ hij
    simpa only [hp, Fin.val_mk] using t
  · intro h
    let p : InducedPath (V × Bool) (LayerAdj R) (m + 1) := {
      vertex := fun i => lifted w k i.val
      distinct := fun i j eq => Fin.ext (lifted_distinct hk simple i.val j.val
        (by have := i.isLt; omega) (by have := j.isLt; omega) eq)
      induced := fun i j hij => h i.val j.val hij (by have := j.isLt; omega)
    }
    exact ⟨p, fun _ => rfl⟩

/-- Characterisation of the actual ordered lift in the product graph. -/
theorem cut_iff {w : Nat → V} {m k : Nat} (hk : k ≤ m)
    (simple : SimpleWord w m) (step : Steps R w m) :
    Realizes R w m k ↔ Straddled R w m k :=
  (realizes_iff_pairs hk simple).trans ((pairs_iff hk simple).trans (arms_iff step))

/-- Every cut between two valid cuts of the same ordered word is valid. -/
theorem cut_interval {w : Nat → V} {m a k b : Nat} (hak : a ≤ k)
    (hkb : k ≤ b) (hbm : b ≤ m) (simple : SimpleWord w m) (step : Steps R w m)
    (left : Realizes R w m a) (right : Realizes R w m b) : Realizes R w m k := by
  have leftChords := (cut_iff (by omega : a ≤ m) simple step).mp left
  have rightChords := (cut_iff hbm simple step).mp right
  apply (cut_iff (by omega : k ≤ m) simple step).mpr
  intro i j gap hj adj
  exact ⟨Nat.lt_of_lt_of_le (leftChords i j gap hj adj).1 hak,
    Nat.lt_of_le_of_lt hkb (rightChords i j gap hj adj).2⟩

#print axioms cut_iff
#print axioms cut_interval

end Hinge249
