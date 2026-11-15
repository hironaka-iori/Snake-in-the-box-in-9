import LayerJoining

set_option Elab.async false

namespace Residual226
open LayerJoining

/-- Two portions of an actual path separated by at least one intervening
index have no common vertex or edge from the earlier portion to the later. -/
theorem separated_path_portions {V : Type} {R : V → V → Prop} {n : Nat}
    (p : InducedPath V R n) (b c : Nat) (gap : b + 2 ≤ c)
    (i j : Fin (n + 1)) (left : i.val ≤ b) (right : c ≤ j.val) :
    p.vertex j ≠ p.vertex i ∧ ¬R (p.vertex i) (p.vertex j) := by
  have indices : i.val < j.val := by omega
  constructor
  · intro equal
    have same := congrArg Fin.val (p.distinct j i equal)
    omega
  · intro edge
    have consecutive := (p.induced i j indices).mp edge
    omega

/-- Any set containing the initial vertex and closed under allowed path
steps contains every vertex of an actual induced path. -/
theorem path_in_closed_set {V : Type} {R : V → V → Prop} {n : Nat}
    (p : InducedPath V R n) (allowed component : V → Prop)
    (fit : ∀ i, allowed (p.vertex i))
    (initial : component (p.vertex ⟨0, Nat.zero_lt_succ n⟩))
    (closed : ∀ u v, component u → allowed v → R u v → component v) :
    ∀ i, component (p.vertex i) := by
  have follows : ∀ k, ∀ bound : k < n + 1,
      component (p.vertex ⟨k, bound⟩) := by
    intro k
    induction k with
    | zero =>
        intro bound
        exact initial
    | succ k ih =>
        intro bound
        have previous : k < n + 1 := Nat.lt_trans (Nat.lt_succ_self k) bound
        apply closed (p.vertex ⟨k, previous⟩) (p.vertex ⟨k + 1, bound⟩)
        · exact ih previous
        · exact fit ⟨k + 1, bound⟩
        · exact (p.induced ⟨k, previous⟩ ⟨k + 1, bound⟩
            (Nat.lt_succ_self k)).mpr rfl
  intro i
  exact follows i.val i.isLt

/-- A compatible second path lies in the initial anchor's residual
component. The closure premise is supplied by a component enumeration. -/
theorem compatible_path_in_component {V : Type} {R : V → V → Prop} {n : Nat}
    (p : InducedPath V R n) (firstVertices : List V) (allowed component : V → Prop)
    (fit : ∀ i, allowed (p.vertex i))
    (separated : ∀ i u, u ∈ firstVertices → p.vertex i ≠ u ∧ ¬R u (p.vertex i))
    (initial : component (p.vertex ⟨0, Nat.zero_lt_succ n⟩))
    (closed : ∀ u v, component u → allowed v →
      (∀ w, w ∈ firstVertices → v ≠ w ∧ ¬R w v) → R u v → component v) :
    ∀ i, component (p.vertex i) := by
  apply path_in_closed_set p
    (fun v => allowed v ∧ ∀ w, w ∈ firstVertices → v ≠ w ∧ ¬R w v) component
  · intro i
    exact ⟨fit i, separated i⟩
  · exact initial
  · intro u v hu hv edge
    exact closed u v hu hv.1 hv.2 edge

/-- Extending the first prefix can only remove residual allowed vertices. -/
theorem residual_shrinks {V : Type} {R : V → V → Prop}
    (firstVertices extended : List V) (included : ∀ u, u ∈ firstVertices → u ∈ extended)
    (allowed : V → Prop) (v : V)
    (residual : allowed v ∧ ∀ u, u ∈ extended → v ≠ u ∧ ¬R u v) :
    allowed v ∧ ∀ u, u ∈ firstVertices → v ≠ u ∧ ¬R u v :=
  ⟨residual.1, fun u hu => residual.2 u (included u hu)⟩

#print axioms separated_path_portions
#print axioms path_in_closed_set
#print axioms compatible_path_in_component
#print axioms residual_shrinks
end Residual226
