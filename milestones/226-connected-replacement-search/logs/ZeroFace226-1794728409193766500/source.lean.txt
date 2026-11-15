import CutParity221
import ResidualCapacity226

set_option Elab.async false

namespace ZeroFace226
open LayerJoining CutParity221

theorem zero_changes_constant (start : Bool) (tail : List Bool)
    (zero : (changes start tail).count true = 0) :
    ∀ value, value ∈ tail → value = start := by
  induction tail generalizing start with
  | nil =>
      intro value member
      exact False.elim (List.not_mem_nil member)
  | cons next rest ih =>
      have same : next = start := by
        cases start <;> cases next <;>
          simp [changes, List.count_cons] at zero ⊢
      subst next
      have rest_zero : (changes start rest).count true = 0 := by
        simpa [changes, List.count_cons] using zero
      intro value member
      rcases List.mem_cons.mp member with equal | remaining
      · exact equal
      · exact ih start rest_zero value remaining

theorem coordinate_walk_constant {V : Type} (coordinate : V → Bool)
    (start : V) (tail : List V)
    (zero : (changes (coordinate start) (tail.map coordinate)).count true = 0) :
    ∀ v, v ∈ tail → coordinate v = coordinate start := by
  intro v member
  exact zero_changes_constant (coordinate start) (tail.map coordinate) zero
    (coordinate v) (List.mem_map.mpr ⟨v, member, rfl⟩)

/-- An actual path with no changes of the selected coordinate must fit
entirely into the initial face of any pool containing its vertices. -/
theorem zero_face_capacity {R : Nat → Nat → Prop} {n : Nat}
    (p : InducedPath Nat R n) (positions : List (Fin (n + 1))) (pool : List Nat)
    (coordinate : Nat → Bool) (distinct : positions.Nodup)
    (count : positions.length = n + 1) (fit : ∀ i, p.vertex i ∈ pool)
    (zero : (changes (coordinate (p.vertex ⟨0, Nat.zero_lt_succ n⟩))
      ((List.ofFn p.vertex).map coordinate)).count true = 0) :
    n + 1 ≤ (pool.filter (fun v =>
      coordinate v == coordinate (p.vertex ⟨0, Nat.zero_lt_succ n⟩))).length := by
  have constant := coordinate_walk_constant coordinate
    (p.vertex ⟨0, Nat.zero_lt_succ n⟩) (List.ofFn p.vertex) zero
  have bound := ResidualCapacity226.colour_capacity p positions pool coordinate
    (coordinate (p.vertex ⟨0, Nat.zero_lt_succ n⟩)) distinct
    (fun i _ => fit i)
    (fun i _ => constant (p.vertex i) (List.mem_ofFn.mpr ⟨i, rfl⟩))
  simpa only [count] using bound

#print axioms zero_changes_constant
#print axioms coordinate_walk_constant
#print axioms zero_face_capacity
end ZeroFace226
