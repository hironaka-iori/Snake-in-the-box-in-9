import LossDomination171

namespace Snake9.Count171
attribute [local instance] Classical.propDecidable

theorem selected_neighbor_count_eq_vertices {m : Nat} (p : Snake m) (q : Vertex) :
    selectedNeighborCount p q =
      (Finset.univ.filter (fun v : Vertex => InPath p v ∧ Adj q v)).card := by
  classical
  unfold selectedNeighborCount
  apply Finset.card_bij (fun a _ => vxor q (unit a))
  · intro a ha
    have hs : InPath p (vxor q (unit a)) := (Finset.mem_filter.mp ha).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, hs, ?_⟩
    apply (adj_vxor q q (vxor q (unit a))).mp
    rw [vxor_self, vxor_cancel]
    exact (adj_zero_iff (unit a)).mpr ⟨a,rfl⟩
  · intro a ha b hb he
    exact unit_injective a b (vxor_injective q he)
  · intro v hv
    have hs := (Finset.mem_filter.mp hv).2
    have hz : Adj 0 (vxor q v) := by
      have ht := (adj_vxor q q v).mpr hs.2
      simpa only [vxor_self] using ht
    obtain ⟨a,he⟩ := (adj_zero_iff (vxor q v)).mp hz
    have hvq : vxor q (unit a) = v := by
      rw [← he, vxor_cancel]
    refine ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, hvq⟩
    simpa only [hvq] using hs.1

#print axioms selected_neighbor_count_eq_vertices
end Snake9.Count171
