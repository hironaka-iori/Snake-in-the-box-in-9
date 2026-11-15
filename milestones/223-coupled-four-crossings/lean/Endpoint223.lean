import LayerJoining

set_option Elab.async false

namespace Endpoint223
open LayerJoining

/-- In an irreflexive undirected graph, two selected neighbours of the
last endpoint of an actual indexed induced path must be the same vertex. -/
theorem last_neighbour_unique {V : Type} {R : V → V → Prop} {m : Nat}
    (p : InducedPath V R m)
    (irreflexive : ∀ v, ¬R v v)
    (symmetric : ∀ u v, R u v → R v u)
    (i j : Fin (m + 1))
    (left : R (p.vertex (Fin.last m)) (p.vertex i))
    (right : R (p.vertex (Fin.last m)) (p.vertex j)) :
    p.vertex i = p.vertex j := by
  have predecessor : ∀ k : Fin (m + 1),
      R (p.vertex (Fin.last m)) (p.vertex k) → k.val + 1 = m := by
    intro k edge
    have different : k.val ≠ m := by
      intro equal_value
      have equal_index : k = Fin.last m := Fin.ext equal_value
      rw [equal_index] at edge
      exact irreflexive _ edge
    have bound := k.isLt
    have order : k.val < (Fin.last m).val := by
      change k.val < m
      omega
    exact (p.induced k (Fin.last m) order).mp (symmetric _ _ edge)
  have hi := predecessor i left
  have hj := predecessor j right
  have same_index : i = j := by
    apply Fin.ext
    omega
  exact congrArg p.vertex same_index

/-- Retaining one selected endpoint neighbour excludes every distinct
neighbour from the entire path. -/
theorem distinct_neighbour_not_selected {V : Type} {R : V → V → Prop} {m : Nat}
    (p : InducedPath V R m)
    (irreflexive : ∀ v, ¬R v v)
    (symmetric : ∀ u v, R u v → R v u)
    (retained : Fin (m + 1)) (candidate : V)
    (retained_edge : R (p.vertex (Fin.last m)) (p.vertex retained))
    (candidate_edge : R (p.vertex (Fin.last m)) candidate)
    (different : candidate ≠ p.vertex retained) :
    ∀ j, p.vertex j ≠ candidate := by
  intro j equal
  have selected_edge : R (p.vertex (Fin.last m)) (p.vertex j) := by
    rw [equal]
    exact candidate_edge
  have same := last_neighbour_unique p irreflexive symmetric j retained
    selected_edge retained_edge
  exact different (equal.symm.trans same)

#print axioms last_neighbour_unique
#print axioms distinct_neighbour_not_selected
end Endpoint223
