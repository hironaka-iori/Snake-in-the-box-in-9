import CommonHoleCounting

namespace Snake9
open Finset Classical
noncomputable section

theorem pair_family_eq_two_of_mem (F : Finset (Finset Coord)) (s t : Finset Coord)
    (hF : F.card=2) (hs : s∈F) (ht : t∈F) (hst : s≠t) : F={s,t} := by
  apply (Finset.eq_of_subset_of_card_le (show ({s,t}:Finset (Finset Coord))⊆F by
    intro u hu
    rcases Finset.mem_insert.mp hu with rfl | hu
    · exact hs
    · exact Finset.mem_singleton.mp hu ▸ ht) (by simp [hF,hst])).symm

theorem outside_edge_two_isolated (C : Finset Coord) (F : Finset (Finset Coord))
    (hC : C.card=3) (hF : F.card=2) (hedge : ∀s∈F,s.card=2)
    (hclean : ∀s∈F,¬s⊆C) (s : Finset Coord) (hs : s∈F) (hdis : Disjoint s C) :
    ∃j : Fin 2 → Coord,Function.Injective j ∧ ∀r,j r∈C ∧ PairIsolated F (j r) := by
  obtain ⟨t,hts,htF,hFt⟩ := pair_family_other_edge F s hF hs
  have hs0 : (s∩C).card=0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_not_mem.mpr
    intro x hx
    exact Finset.disjoint_left.mp hdis (Finset.mem_inter.mp hx).1 (Finset.mem_inter.mp hx).2
  have ht1 := two_edge_inter_card t C C (hedge t htF) (Finset.Subset.refl _) (hclean t htF)
  have hb := two_edge_union_inter_bound F C t s (by rw [hFt]; exact Finset.pair_comm _ _)
    (by omega) (by omega)
  have he : C∩F.biUnion id=(s∩C)∪(t∩C) := by ext x; simp [hFt]; tauto
  have hb' := Finset.card_union_le (s∩C) (t∩C)
  rw [←he] at hb'
  exact family_isolated_embedding F C 2 (by omega)

theorem fork_family_two_isolated (C : Finset Coord) (F : Finset (Finset Coord))
    (i j k : Coord) (hC : C.card=3) (hi : i∉C) (hj : j∉C)
    (hF : F={{i,k},{j,k}}) :
    ∃u : Fin 2 → Coord,Function.Injective u ∧ ∀r,u r∈C ∧ PairIsolated F (u r) := by
  have hsub : C∩F.biUnion id⊆{k} := by
    intro x hx
    obtain ⟨hxC,hxF⟩ := Finset.mem_inter.mp hx
    simp only [hF,Finset.mem_biUnion,Finset.mem_insert,Finset.mem_singleton] at hxF
    obtain ⟨s,hs,hxs⟩ := hxF
    rcases hs with rfl | rfl
    · simp only [id_eq,Finset.mem_insert,Finset.mem_singleton] at hxs
      rcases hxs with rfl | rfl
      · exact False.elim (hi hxC)
      · simp
    · simp only [id_eq,Finset.mem_insert,Finset.mem_singleton] at hxs
      rcases hxs with rfl | rfl
      · exact False.elim (hj hxC)
      · simp
  have hb : (C∩F.biUnion id).card≤1 := (Finset.card_le_card hsub).trans_eq (Finset.card_singleton k)
  exact family_isolated_embedding F C 2 (by omega)

theorem two_outside_edges_three_isolated (C : Finset Coord) (F : Finset (Finset Coord))
    (s t : Finset Coord) (hC : C.card=3) (hF : F={s,t})
    (hs : Disjoint s C) (ht : Disjoint t C) :
    ∃u : Fin 3 → Coord,Function.Injective u ∧ ∀r,u r∈C ∧ PairIsolated F (u r) := by
  have he : C∩F.biUnion id=∅ := by
    apply Finset.eq_empty_iff_forall_not_mem.mpr
    intro x hx
    obtain ⟨hxC,hxF⟩ := Finset.mem_inter.mp hx
    obtain ⟨v,hv,hxv⟩ := Finset.mem_biUnion.mp hxF
    rw [hF] at hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact Finset.disjoint_left.mp hs hxv hxC
    · have he := Finset.mem_singleton.mp hv
      exact Finset.disjoint_left.mp ht (he ▸ hxv) hxC
  exact family_isolated_embedding F C 3 (by rw [he,Finset.card_empty,hC])

#print axioms outside_edge_two_isolated
#print axioms fork_family_two_isolated
#print axioms two_outside_edges_three_isolated
end
end Snake9
