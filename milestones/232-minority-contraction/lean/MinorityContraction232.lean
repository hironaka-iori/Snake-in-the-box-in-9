import ColourContraction231
import TwoCrossings188

set_option Elab.async false

namespace MinorityContraction232
open LayerJoining

/-- A label with one chosen neighbour cannot equal an internal label
having the two consecutive chosen neighbours. -/
theorem singleton_label_ne_internal {V : Type} {R : V → V → Prop} {k : Nat}
    (u : Fin (k + 1) → V) (z : Fin k → V)
    (symmetric : ∀ v w, R v w → R w v)
    (cross : ∀ i j, R (u i) (z j) ↔ i.val = j.val ∨ i.val = j.val + 1)
    (s : V) (e : Fin (k + 1))
    (singleton : ∀ i, R s (u i) ↔ i.val = e.val) :
    ∀ j, s ≠ z j := by
  intro j equal
  have left : R s (u ⟨j.val, by have hj := j.isLt; omega⟩) := by
    rw [equal]
    exact symmetric _ _ ((cross ⟨j.val, by omega⟩ j).mpr (Or.inl rfl))
  have right : R s (u ⟨j.val + 1, by have hj := j.isLt; omega⟩) := by
    rw [equal]
    exact symmetric _ _ ((cross ⟨j.val + 1, by omega⟩ j).mpr (Or.inr rfl))
  have hl := (singleton ⟨j.val, by omega⟩).mp left
  have hr := (singleton ⟨j.val + 1, by omega⟩).mp right
  simp only [Fin.val_mk] at hl hr
  omega

/-- Attach two new endpoint vertices to an actual induced path, using
the accepted appendEdge constructor at each end. -/
def addEndpoints {V : Type} {R : V → V → Prop} {n : Nat}
    (p : InducedPath V R n) (s t : V)
    (s_new : ∀ i, s ≠ p.vertex i) (t_new : ∀ i, p.vertex i ≠ t)
    (distinct_endpoints : s ≠ t)
    (s_first : ∀ i, R s (p.vertex i) ↔ i.val = 0)
    (t_last : ∀ i, R (p.vertex i) t ↔ i.val = n)
    (nonadjacent_endpoints : ¬ R s t) : InducedPath V R (n + 2) := by
  let first : InducedPath V R 0 := {
    vertex := fun _ => s
    distinct := by intro i j _; apply Fin.ext; have hi := i.isLt; have hj := j.isLt; omega
    induced := by intro i j order; have hi := i.isLt; have hj := j.isLt; omega
  }
  let last : InducedPath V R 0 := {
    vertex := fun _ => t
    distinct := by intro i j _; apply Fin.ext; have hi := i.isLt; have hj := j.isLt; omega
    induced := by intro i j order; have hi := i.isLt; have hj := j.isLt; omega
  }
  have right_disjoint : ∀ i j, p.vertex i ≠ last.vertex j := by
    intro i j
    exact t_new i
  have right_cross : ∀ i j,
      R (p.vertex i) (last.vertex j) ↔ i.val = n ∧ j.val = 0 := by
    intro i j
    change R (p.vertex i) t ↔ _
    rw [t_last]
    have hj := j.isLt
    omega
  let right := Dimensional188.appendEdge p last right_disjoint right_cross
  have left_disjoint : ∀ i j, first.vertex i ≠ right.vertex j := by
    intro i j
    change s ≠ Dimensional188.appendVertex p last j
    unfold Dimensional188.appendVertex
    split
    · exact s_new _
    · exact distinct_endpoints
  have left_cross : ∀ i j,
      R (first.vertex i) (right.vertex j) ↔ i.val = 0 ∧ j.val = 0 := by
    intro i j
    change R s (Dimensional188.appendVertex p last j) ↔ _
    unfold Dimensional188.appendVertex
    split
    · rw [s_first]
      simp only [Fin.val_mk]
      have hi := i.isLt
      omega
    · change R s t ↔ _
      constructor
      · intro edge
        exact False.elim (nonadjacent_endpoints edge)
      · intro positions
        omega
  have result := Dimensional188.appendEdge first right left_disjoint left_cross
  simpa only [Nat.zero_add, Nat.add_zero, Nat.add_assoc] using result

/-- A simple ordering of the minority class, internal degree-two labels,
and two endpoint degree-one labels lift to an induced path of length 2k+2. -/
def minorityPath {V : Type} {R : V → V → Prop} {k : Nat}
    (u : Fin (k + 1) → V) (z : Fin k → V) (s t : V)
    (symmetric : ∀ v w, R v w → R w v)
    (u_distinct : ∀ i j, u i = u j → i = j)
    (z_distinct : ∀ i j, z i = z j → i = j)
    (disjoint : ∀ i j, u i ≠ z j)
    (u_nonadjacent : ∀ i j, ¬ R (u i) (u j))
    (z_nonadjacent : ∀ i j, ¬ R (z i) (z j))
    (cross : ∀ i j, R (u i) (z j) ↔ i.val = j.val ∨ i.val = j.val + 1)
    (s_outside : ∀ i, s ≠ u i) (t_outside : ∀ i, u i ≠ t)
    (distinct_endpoints : s ≠ t)
    (s_neighbours : ∀ i, R s (u i) ↔ i.val = 0)
    (t_neighbours : ∀ i, R (u i) t ↔ i.val = k)
    (s_labels_nonadjacent : ∀ j, ¬ R s (z j))
    (t_labels_nonadjacent : ∀ j, ¬ R (z j) t)
    (nonadjacent_endpoints : ¬ R s t) :
    InducedPath V R (2 * k + 2) := by
  let p := ColourContraction231.interleave u z symmetric u_distinct z_distinct
    disjoint u_nonadjacent z_nonadjacent cross
  have s_internal := singleton_label_ne_internal u z symmetric cross s
    ⟨0, by omega⟩ s_neighbours
  have t_reverse : ∀ i, R t (u i) ↔ i.val = k := by
    intro i
    exact ⟨fun edge => (t_neighbours i).mp (symmetric _ _ edge),
      fun last => symmetric _ _ ((t_neighbours i).mpr last)⟩
  have t_internal := singleton_label_ne_internal u z symmetric cross t
    ⟨k, by omega⟩ t_reverse
  have s_new : ∀ i, s ≠ p.vertex i := by
    intro i
    change s ≠ ColourContraction231.interleavedVertex u z i
    unfold ColourContraction231.interleavedVertex
    split
    · exact s_outside _
    · exact s_internal _
  have t_new : ∀ i, p.vertex i ≠ t := by
    intro i
    change ColourContraction231.interleavedVertex u z i ≠ t
    unfold ColourContraction231.interleavedVertex
    split
    · exact t_outside _
    · intro equal
      exact t_internal _ equal.symm
  have s_first : ∀ i, R s (p.vertex i) ↔ i.val = 0 := by
    intro i
    change R s (ColourContraction231.interleavedVertex u z i) ↔ _
    unfold ColourContraction231.interleavedVertex
    split
    · rw [s_neighbours]
      simp only [Fin.val_mk]
      omega
    · constructor
      · intro edge
        exact False.elim (s_labels_nonadjacent _ edge)
      · intro position
        omega
  have t_last : ∀ i, R (p.vertex i) t ↔ i.val = 2 * k := by
    intro i
    change R (ColourContraction231.interleavedVertex u z i) t ↔ _
    unfold ColourContraction231.interleavedVertex
    split
    · rw [t_neighbours]
      simp only [Fin.val_mk]
      omega
    · constructor
      · intro edge
        exact False.elim (t_labels_nonadjacent _ edge)
      · intro position
        omega
  exact addEndpoints p s t s_new t_new distinct_endpoints s_first t_last
    nonadjacent_endpoints

/-- In an actual even-length induced path, each endpoint has exactly its
adjacent odd-position vertex as neighbour among all odd positions. -/
theorem endpoint_singleton_neighbours {V : Type} {R : V → V → Prop} {k : Nat}
    (p : InducedPath V R (2 * k + 2)) (i : Fin (k + 1)) :
    (R (p.vertex ⟨0, by omega⟩)
      (p.vertex ⟨2 * i.val + 1, by have hi := i.isLt; omega⟩) ↔ i.val = 0) ∧
    (R (p.vertex ⟨2 * i.val + 1, by have hi := i.isLt; omega⟩)
      (p.vertex ⟨2 * k + 2, by omega⟩) ↔ i.val = k) := by
  constructor
  · rw [p.induced ⟨0, by omega⟩
      ⟨2 * i.val + 1, by have hi := i.isLt; omega⟩ (by simp only [Fin.val_mk]; omega)]
    simp only [Fin.val_mk]
    omega
  · rw [p.induced ⟨2 * i.val + 1, by have hi := i.isLt; omega⟩
      ⟨2 * k + 2, by omega⟩ (by have hi := i.isLt; simp only [Fin.val_mk]; omega)]
    simp only [Fin.val_mk]
    omega

#print axioms singleton_label_ne_internal
#print axioms addEndpoints
#print axioms minorityPath
#print axioms endpoint_singleton_neighbours

end MinorityContraction232
