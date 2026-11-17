import Std

set_option Elab.async false

namespace ColourExchange234

/-- Exact update of a label's selected neighbours after removing d and
inserting a. This identity needs no finiteness or graph assumptions. -/
theorem exchanged_neighbours_iff {V Label : Type}
    (C : Label → V → Prop) (old : V → Prop)
    (z : Label) (d a v : V) :
    (((old v ∧ v ≠ d) ∨ v = a) ∧ C z v) ↔
      ((old v ∧ C z v) ∧ v ≠ d) ∨ (v = a ∧ C z a) := by
  constructor
  · rintro ⟨retained | inserted, neighbour⟩
    · exact Or.inl ⟨⟨retained.1, neighbour⟩, retained.2⟩
    · exact Or.inr ⟨inserted, by simpa only [inserted] using neighbour⟩
  · rintro (⟨⟨selected, neighbour⟩, different⟩ | ⟨inserted, neighbour⟩)
    · exact ⟨Or.inl ⟨selected, different⟩, neighbour⟩
    · exact ⟨Or.inr inserted, by simpa only [inserted] using neighbour⟩

/-- For a genuine exchange, complete neighbour sets are unchanged exactly
for labels incident to neither the removed nor the inserted vertex. -/
theorem neighbours_unchanged_iff {V Label : Type}
    (C : Label → V → Prop) (old : V → Prop)
    (z : Label) (d a : V) (removed : old d) (outside : ¬ old a) :
    (∀ v, (((old v ∧ v ≠ d) ∨ v = a) ∧ C z v) ↔ old v ∧ C z v) ↔
      ¬ C z d ∧ ¬ C z a := by
  have different : d ≠ a := by
    intro equal
    exact outside (by simpa only [equal] using removed)
  constructor
  · intro unchanged
    constructor
    · intro neighbour
      have after := (unchanged d).mpr ⟨removed, neighbour⟩
      rcases after.1 with retained | inserted
      · exact retained.2 rfl
      · exact different inserted
    · intro neighbour
      have before := (unchanged a).mp ⟨Or.inr rfl, neighbour⟩
      exact outside before.1
  · rintro ⟨removed_nonadjacent, inserted_nonadjacent⟩ v
    constructor
    · rintro ⟨retained | inserted, neighbour⟩
      · exact ⟨retained.1, neighbour⟩
      · exact False.elim (inserted_nonadjacent
          (by simpa only [inserted] using neighbour))
    · rintro ⟨selected, neighbour⟩
      have retained : v ≠ d := by
        intro equal
        exact removed_nonadjacent (by simpa only [equal] using neighbour)
      exact ⟨Or.inl ⟨selected, retained⟩, neighbour⟩

/-- Exact endpoint-label update: its old singleton is retained unless
it is deleted, and the inserted vertex is added exactly when adjacent. -/
theorem singleton_after_exchange {V Label : Type}
    (C : Label → V → Prop) (old : V → Prop)
    (z : Label) (d a b : V)
    (singleton : ∀ v, (old v ∧ C z v) ↔ v = b) :
    ∀ v, (((old v ∧ v ≠ d) ∨ v = a) ∧ C z v) ↔
      (v = b ∧ v ≠ d) ∨ (v = a ∧ C z a) := by
  intro v
  rw [exchanged_neighbours_iff C old z d a v, singleton v]

/-- Exact internal-label update, retaining its full neighbour identities.
The two old neighbours are distinct; the statement does not assume that
the updated label still has degree two. -/
theorem two_neighbours_after_exchange {V Label : Type}
    (C : Label → V → Prop) (old : V → Prop)
    (z : Label) (d a b c : V) (_distinct : b ≠ c)
    (pair : ∀ v, (old v ∧ C z v) ↔ v = b ∨ v = c) :
    ∀ v, (((old v ∧ v ≠ d) ∨ v = a) ∧ C z v) ↔
      ((v = b ∨ v = c) ∧ v ≠ d) ∨ (v = a ∧ C z a) := by
  intro v
  rw [exchanged_neighbours_iff C old z d a v, pair v]

#print axioms exchanged_neighbours_iff
#print axioms neighbours_unchanged_iff
#print axioms singleton_after_exchange
#print axioms two_neighbours_after_exchange

end ColourExchange234
