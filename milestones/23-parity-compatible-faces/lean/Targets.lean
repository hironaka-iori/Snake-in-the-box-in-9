import DfsParity
import PathStructure

namespace Snake9.ConstructionTargets

theorem improvement_iff_192 :
    (∃ m, 191 < m ∧ Nonempty (Snake m)) ↔ Nonempty (Snake 192) := by
  constructor
  · rintro ⟨m,hm,⟨p⟩⟩
    exact ⟨takePrefix p (by omega)⟩
  · intro hp
    exact ⟨192,by decide,hp⟩

theorem from_193 (p : Snake 193) : Nonempty (Snake 192) :=
  ⟨takePrefix p (by decide)⟩

theorem fixed_endpoints_improvement_at_least_193 {m : Nat}
    (p : Snake 191) (q : Snake m)
    (h0 : p.vertex 0 = q.vertex 0)
    (h1 : p.vertex (Fin.last 191) = q.vertex (Fin.last m))
    (hm : 191 < m) : 193 ≤ m ∧ m % 2 = 1 := by
  have h := same_endpoints_same_parity p q h0 h1
  omega

theorem exclude_neighbor_of_fixed_interior {m : Nat} (p : Snake m)
    {v a b c : Vertex} (hv : InPath p v) (ha : InPath p a) (hb : InPath p b)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hva : Adj v a) (hvb : Adj v b) (hvc : Adj v c) : ¬ InPath p c := by
  intro hc
  rcases selected_three_neighbors_repeat p hv ha hb hc hva hvb hvc with h | h | h
  · exact hab h
  · exact hac h
  · exact hbc h

#print axioms improvement_iff_192
#print axioms from_193
#print axioms fixed_endpoints_improvement_at_least_193
#print axioms exclude_neighbor_of_fixed_interior
end Snake9.ConstructionTargets
