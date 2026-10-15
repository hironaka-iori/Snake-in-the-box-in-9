import SingletonSquareLemma
import Mathlib.Tactic

namespace Snake9

theorem exists_good_group {m n : Nat} (p : Snake m)
    (v : Fin 3 → Fin n → Vertex)
    (hv : ∀ k r, InPath p (v k r))
    (hdis : ∀ k l, k ≠ l → ∀ r s, v k r ≠ v l s) :
    ∃ k, ∀ r, ¬ AtMostOneNeighbor p (v k r) := by
  classical
  by_contra h
  push_neg at h
  obtain ⟨r₀, hr₀⟩ := h 0
  obtain ⟨r₁, hr₁⟩ := h 1
  obtain ⟨r₂, hr₂⟩ := h 2
  rcases three_low_degree_vertices_repeat p (hv 0 r₀) (hv 1 r₁) (hv 2 r₂)
      hr₀ hr₁ hr₂ with he | he | he
  · exact hdis 0 1 (by decide) r₀ r₁ he
  · exact hdis 0 2 (by decide) r₀ r₂ he
  · exact hdis 1 2 (by decide) r₁ r₂ he

theorem force_two_neighbors {m : Nat} (p : Snake m) (v a b : Vertex)
    (hnot : ¬ AtMostOneNeighbor p v)
    (cover : ∀ w, InPath p w → Adj v w → w=a ∨ w=b) :
    InPath p a ∧ InPath p b := by
  classical
  unfold AtMostOneNeighbor at hnot
  push_neg at hnot
  obtain ⟨u,w,hu,hw,hvu,hvw,hne⟩ := hnot
  rcases cover u hu hvu with h | h <;> rcases cover w hw hvw with h' | h'
  · exact False.elim (hne (h.trans h'.symm))
  · exact ⟨h ▸ hu,h' ▸ hw⟩
  · exact ⟨h' ▸ hw,h ▸ hu⟩
  · exact False.elim (hne (h.trans h'.symm))

#print axioms exists_good_group
#print axioms force_two_neighbors
end Snake9
