import Std

set_option Elab.async false

namespace IsolationDeletion233

/-- If deletion removes none of a label's old selected neighbours, an
exact two-neighbour witness after deletion was already a witness before. -/
theorem two_neighbour_witness_before_deletion {V Label : Type}
    (C : Label → V → Prop) (old retained : V → Prop)
    (subset : ∀ v, retained v → old v)
    (y : Label) (x z : V)
    (local_retention : ∀ v, old v → C y v → retained v)
    (after : ∀ v, (retained v ∧ C y v) ↔ v = x ∨ v = z) :
    ∀ v, (old v ∧ C y v) ↔ v = x ∨ v = z := by
  intro v
  constructor
  · rintro ⟨hv, neighbour⟩
    exact (after v).mp ⟨local_retention v hv neighbour, neighbour⟩
  · intro endpoint
    obtain ⟨hv, neighbour⟩ := (after v).mpr endpoint
    exact ⟨subset v hv, neighbour⟩

/-- Isolation cannot be repaired without removing an old selected
neighbour of some label adjacent to the isolated vertex. The exact
two-neighbour witness includes membership of both selected endpoints. -/
theorem isolation_preserved_by_local_retention {V Label : Type}
    (C : Label → V → Prop) (old retained : V → Prop)
    (subset : ∀ v, retained v → old v) (x : V)
    (isolated : ¬ ∃ z y, z ≠ x ∧
      ∀ v, (old v ∧ C y v) ↔ v = x ∨ v = z)
    (local_retention : ∀ y, C y x →
      ∀ v, old v → C y v → retained v) :
    ¬ ∃ z y, z ≠ x ∧
      ∀ v, (retained v ∧ C y v) ↔ v = x ∨ v = z := by
  rintro ⟨z, y, different, after⟩
  have incident : C y x := ((after x).mpr (Or.inl rfl)).2
  have before := two_neighbour_witness_before_deletion C old retained subset y x z
    (local_retention y incident) after
  exact isolated ⟨z, y, different, before⟩

#print axioms two_neighbour_witness_before_deletion
#print axioms isolation_preserved_by_local_retention

end IsolationDeletion233
