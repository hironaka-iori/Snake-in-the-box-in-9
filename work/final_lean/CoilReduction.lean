import Snake9

namespace Snake9

structure Coil (m : Nat) where
  vertex : Fin m → Vertex
  distinct : ∀ i j, vertex i = vertex j → i = j
  induced : ∀ i j, i.val < j.val →
    (Adj (vertex i) (vertex j) ↔ i.val + 1 = j.val ∨ (i.val = 0 ∧ j.val + 1 = m))

/- Deleting the final vertex of an induced cycle leaves an induced path. -/
def deleteLastOfCoil {m : Nat} (c : Coil (m + 2)) : Snake m where
  vertex i := c.vertex ⟨i.val, by omega⟩
  distinct i j eq := by
    have e := c.distinct ⟨i.val, by omega⟩ ⟨j.val, by omega⟩ eq
    apply Fin.ext
    exact congrArg (fun x : Fin (m + 2) => x.val) e
  induced i j hij := by
    have h := c.induced ⟨i.val, by omega⟩ ⟨j.val, by omega⟩ hij
    change Adj _ _ ↔ i.val + 1 = j.val ∨ (i.val = 0 ∧ j.val + 1 = m + 2) at h
    have hj := j.isLt
    constructor
    · intro ha
      have hd := h.mp ha
      omega
    · intro he
      exact h.mpr (Or.inl he)

theorem coil194_disproves_191 (c : Coil 194) :
    Nonempty (Snake 192) ∧ ¬ (∀ m, Nonempty (Snake m) → m ≤ 191) := by
  have hs : Nonempty (Snake 192) := ⟨deleteLastOfCoil c⟩
  refine ⟨hs, ?_⟩
  intro h
  have := h 192 hs
  omega

#print axioms deleteLastOfCoil
#print axioms coil194_disproves_191
end Snake9
