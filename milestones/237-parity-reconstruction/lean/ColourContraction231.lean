import LayerJoining

set_option Elab.async false

namespace ColourContraction231
open LayerJoining

def interleavedVertex {V : Type} {k : Nat}
    (u : Fin (k + 1) → V) (z : Fin k → V)
    (i : Fin (2 * k + 1)) : V :=
  if h : i.val % 2 = 0 then
    u ⟨i.val / 2, by have hi := i.isLt; omega⟩
  else
    z ⟨i.val / 2, by have hi := i.isLt; omega⟩

/-- Construct the induced path from a simple ordering of one colour class
and distinct opposite-colour labels with exactly the required neighbours. -/
def interleave {V : Type} {R : V → V → Prop} {k : Nat}
    (u : Fin (k + 1) → V) (z : Fin k → V)
    (symmetric : ∀ v w, R v w → R w v)
    (u_distinct : ∀ i j, u i = u j → i = j)
    (z_distinct : ∀ i j, z i = z j → i = j)
    (disjoint : ∀ i j, u i ≠ z j)
    (u_nonadjacent : ∀ i j, ¬ R (u i) (u j))
    (z_nonadjacent : ∀ i j, ¬ R (z i) (z j))
    (cross : ∀ i j, R (u i) (z j) ↔ i.val = j.val ∨ i.val = j.val + 1) :
    InducedPath V R (2 * k) where
  vertex := interleavedVertex u z
  distinct i j equal := by
    unfold interleavedVertex at equal
    split at equal <;> split at equal
    · have hi := u_distinct _ _ equal
      have hv := congrArg Fin.val hi
      apply Fin.ext
      simp only [Fin.val_mk] at hv
      omega
    · exact False.elim (disjoint _ _ equal)
    · exact False.elim (disjoint _ _ equal.symm)
    · have hi := z_distinct _ _ equal
      have hv := congrArg Fin.val hi
      apply Fin.ext
      simp only [Fin.val_mk] at hv
      omega
  induced i j order := by
    unfold interleavedVertex
    split <;> split
    · constructor
      · intro edge
        exact False.elim (u_nonadjacent _ _ edge)
      · intro next
        omega
    · rw [cross]
      simp only [Fin.val_mk]
      omega
    · have reverse :
          R (z ⟨i.val / 2, by omega⟩) (u ⟨j.val / 2, by omega⟩) ↔
          R (u ⟨j.val / 2, by omega⟩) (z ⟨i.val / 2, by omega⟩) :=
        ⟨symmetric _ _, symmetric _ _⟩
      rw [reverse, cross]
      simp only [Fin.val_mk]
      omega
    · constructor
      · intro edge
        exact False.elim (z_nonadjacent _ _ edge)
      · intro next
        omega

/-- An actual even-length induced path has exactly the contracted
neighbour relation between its even and odd positions. -/
theorem even_odd_adjacency {V : Type} {R : V → V → Prop} {k : Nat}
    (p : InducedPath V R (2 * k))
    (symmetric : ∀ v w, R v w → R w v)
    (i : Fin (k + 1)) (j : Fin k) :
    R (p.vertex ⟨2 * i.val, by have hi := i.isLt; omega⟩)
      (p.vertex ⟨2 * j.val + 1, by have hj := j.isLt; omega⟩) ↔
      i.val = j.val ∨ i.val = j.val + 1 := by
  let ei : Fin (2 * k + 1) := ⟨2 * i.val, by have hi := i.isLt; omega⟩
  let oj : Fin (2 * k + 1) := ⟨2 * j.val + 1, by have hj := j.isLt; omega⟩
  change R (p.vertex ei) (p.vertex oj) ↔ _
  by_cases order : ei.val < oj.val
  · rw [p.induced ei oj order]
    dsimp [ei, oj] at *
    omega
  · have reversed : oj.val < ei.val := by
      dsimp [ei, oj] at *
      omega
    have symmetry : R (p.vertex ei) (p.vertex oj) ↔ R (p.vertex oj) (p.vertex ei) :=
      ⟨symmetric _ _, symmetric _ _⟩
    rw [symmetry, p.induced oj ei reversed]
    dsimp [ei, oj] at *
    omega

/-- The two extracted vertex sequences are separately injective and
disjoint because their original positions are distinct. -/
theorem extracted_distinct {V : Type} {R : V → V → Prop} {k : Nat}
    (p : InducedPath V R (2 * k)) :
    (∀ i j : Fin (k + 1),
      p.vertex ⟨2 * i.val, by have hi := i.isLt; omega⟩ =
        p.vertex ⟨2 * j.val, by have hj := j.isLt; omega⟩ → i = j) ∧
    (∀ i j : Fin k,
      p.vertex ⟨2 * i.val + 1, by have hi := i.isLt; omega⟩ =
        p.vertex ⟨2 * j.val + 1, by have hj := j.isLt; omega⟩ → i = j) ∧
    (∀ (i : Fin (k + 1)) (j : Fin k),
      p.vertex ⟨2 * i.val, by have hi := i.isLt; omega⟩ ≠
        p.vertex ⟨2 * j.val + 1, by have hj := j.isLt; omega⟩) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j equal
    have hv := congrArg Fin.val (p.distinct _ _ equal)
    apply Fin.ext
    simp only [Fin.val_mk] at hv
    omega
  · intro i j equal
    have hv := congrArg Fin.val (p.distinct _ _ equal)
    apply Fin.ext
    simp only [Fin.val_mk] at hv
    omega
  · intro i j equal
    have hv := congrArg Fin.val (p.distinct _ _ equal)
    simp only [Fin.val_mk] at hv
    omega

/-- Same-parity positions of an induced path in an irreflexive undirected
graph are nonadjacent, including the case of equal positions. -/
theorem same_parity_nonadjacent {V : Type} {R : V → V → Prop} {n : Nat}
    (p : InducedPath V R n)
    (irreflexive : ∀ v, ¬ R v v)
    (symmetric : ∀ v w, R v w → R w v)
    (i j : Fin (n + 1)) (parity : i.val % 2 = j.val % 2) :
    ¬ R (p.vertex i) (p.vertex j) := by
  intro edge
  by_cases forward : i.val < j.val
  · have next := (p.induced i j forward).mp edge
    omega
  · by_cases backward : j.val < i.val
    · have next := (p.induced j i backward).mp (symmetric _ _ edge)
      omega
    · have equal : i = j := Fin.ext (by omega)
      exact irreflexive (p.vertex j) (by simpa only [equal] using edge)

#print axioms interleave
#print axioms even_odd_adjacency
#print axioms extracted_distinct
#print axioms same_parity_nonadjacent

end ColourContraction231
