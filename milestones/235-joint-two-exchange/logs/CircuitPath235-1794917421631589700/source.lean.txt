import LayerJoining

set_option Elab.async false

namespace CircuitPath235
open LayerJoining

/-- The two directional arc indicators sum to the Boolean product of
the endpoint selections. Naturals supply their nonnegativity. -/
theorem boolean_edge_constraints (x y forward backward : Nat)
    (hx : x ≤ 1) (hy : y ≤ 1) :
    (forward + backward ≤ x ∧ forward + backward ≤ y ∧
      x + y - 1 ≤ forward + backward) ↔ forward + backward = x * y := by
  have x_cases : x = 0 ∨ x = 1 := by omega
  have y_cases : y = 0 ∨ y = 1 := by omega
  rcases x_cases with rfl | rfl <;>
    rcases y_cases with rfl | rfl <;> omega

/-- A selected adjacent pair uses exactly one direction. -/
theorem one_direction (forward backward : Nat) (total : forward + backward = 1) :
    (forward = 1 ∧ backward = 0) ∨ (forward = 0 ∧ backward = 1) := by
  omega

/-- Exact successor arcs rule out repeated ordered vertices. A repeated
earlier vertex would give its outgoing arc to the later position too. -/
theorem successor_arcs_injective {V : Type} {m : Nat}
    (vertex : Fin (m + 1) → V) (arc : V → V → Prop)
    (order : ∀ i j, arc (vertex i) (vertex j) ↔ i.val + 1 = j.val) :
    ∀ i j, vertex i = vertex j → i = j := by
  have before_last : ∀ i j : Fin (m + 1),
      i.val < m → vertex i = vertex j → i = j := by
    intro i j earlier equal
    let next : Fin (m + 1) := ⟨i.val + 1, by omega⟩
    have edge : arc (vertex i) (vertex next) := (order i next).mpr rfl
    have repeated_edge : arc (vertex j) (vertex next) := by
      rw [← equal]
      exact edge
    have positions := (order j next).mp repeated_edge
    apply Fin.ext
    dsimp [next] at positions
    omega
  intro i j equal
  by_cases forward : i.val < j.val
  · exact before_last i j (by have hj := j.isLt; omega) equal
  · by_cases backward : j.val < i.val
    · exact (before_last j i (by have hi := i.isLt; omega) equal.symm).symm
    · exact Fin.ext (by omega)

/-- Construct an actual induced path from supported successor arcs and
coverage of all adjacent distinct ordered vertices. Neither injectivity
nor the desired inducedness conclusion is assumed. -/
def path_of_ordered_arcs {V : Type} {R : V → V → Prop} {m : Nat}
    (vertex : Fin (m + 1) → V) (arc : V → V → Prop)
    (supported : ∀ v w, arc v w → R v w)
    (covered : ∀ i j, vertex i ≠ vertex j → R (vertex i) (vertex j) →
      arc (vertex i) (vertex j) ∨ arc (vertex j) (vertex i))
    (order : ∀ i j, arc (vertex i) (vertex j) ↔ i.val + 1 = j.val) :
    InducedPath V R m where
  vertex := vertex
  distinct := successor_arcs_injective vertex arc order
  induced i j increasing := by
    constructor
    · intro adjacent
      have different : vertex i ≠ vertex j := by
        intro equal
        have same := successor_arcs_injective vertex arc order i j equal
        have positions := congrArg Fin.val same
        omega
      rcases covered i j different adjacent with forward | backward
      · exact (order i j).mp forward
      · have positions := (order j i).mp backward
        omega
    · intro consecutive
      exact supported _ _ ((order i j).mpr consecutive)

#print axioms boolean_edge_constraints
#print axioms one_direction
#print axioms successor_arcs_injective
#print axioms path_of_ordered_arcs

end CircuitPath235
