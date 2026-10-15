import NormalizeOneTwo

namespace Snake9
open scoped BigOperators
open Finset Classical
noncomputable section
set_option maxHeartbeats 1200000

def selectedEndpoints {m : Nat} (p : Snake m) : Finset Vertex :=
  Finset.univ.filter (fun v => InPath p v ∧ AtMostOneNeighbor p v)

theorem selectedEndpoints_card {m : Nat} (p : Snake m) : (selectedEndpoints p).card ≤ 2 := by
  have hs : selectedEndpoints p ⊆ {p.vertex 0,p.vertex (Fin.last m)} := by
    intro v hv
    obtain ⟨hv,hl⟩ := (Finset.mem_filter.mp hv).2
    obtain ⟨i,rfl⟩ := hv
    rcases low_degree_index_is_endpoint p i hl with h | h
    · have he : i = 0 := Fin.ext h
      simp [he]
    · have he : i = Fin.last m := Fin.ext h
      simp [he]
  exact (Finset.card_le_card hs).trans Finset.card_le_two

theorem two_endpoint_images_card {m : Nat} (p : Snake m)
    {α β : Type} [DecidableEq α] [DecidableEq β]
    (I : Finset α) (J : Finset β) (f : α → Vertex) (g : β → Vertex)
    (hfi : Set.InjOn f I) (hgi : Set.InjOn g J)
    (hfs : ∀ i ∈ I, InPath p (f i) ∧ AtMostOneNeighbor p (f i))
    (hgs : ∀ j ∈ J, InPath p (g j) ∧ AtMostOneNeighbor p (g j))
    (hdis : ∀ i ∈ I, ∀ j ∈ J, f i ≠ g j) : I.card + J.card ≤ 2 := by
  have hs : I.image f ∪ J.image g ⊆ selectedEndpoints p := by
    intro v hv
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    rcases Finset.mem_union.mp hv with hv | hv
    · obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hv
      exact hfs i hi
    · obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hv
      exact hgs j hj
  have hd : Disjoint (I.image f) (J.image g) := by
    apply Finset.disjoint_left.mpr
    intro v hv hw
    obtain ⟨i,hi,he⟩ := Finset.mem_image.mp hv
    obtain ⟨j,hj,he'⟩ := Finset.mem_image.mp hw
    exact hdis i hi j hj (he.trans he'.symm)
  have hc := (Finset.card_le_card hs).trans (selectedEndpoints_card p)
  rw [Finset.card_union_of_disjoint hd,Finset.card_image_of_injOn hfi,
    Finset.card_image_of_injOn hgi] at hc
  exact hc

theorem five_not_covered_by_two_endpoints {α : Type} [DecidableEq α]
    (W I : Finset α) (J : Finset (Finset α)) (hW : W.card = 5)
    (hcost : I.card + J.card ≤ 2) (hpair : ∀ s ∈ J, s.card = 2)
    (hcover : ∀ i ∈ W, i ∈ I ∨ ∃ s ∈ J, i ∈ s) : False := by
  have hs : W ⊆ I ∪ J.biUnion id := by
    intro i hi
    rcases hcover i hi with h | ⟨s,hs,hi⟩
    · exact Finset.mem_union_left _ h
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨s,hs,hi⟩)
  have hb : (J.biUnion id).card ≤ 2 * J.card := by
    calc
      _ ≤ ∑ s ∈ J, s.card := Finset.card_biUnion_le
      _ = J.card * 2 := Finset.sum_const_nat hpair
      _ = _ := Nat.mul_comm _ _
  have hu := Finset.card_union_le I (J.biUnion id)
  have hc := Finset.card_le_card hs
  omega

def edgeVertex (s : Finset Coord) : Vertex :=
  if hs : s.card = 2 then
    pair (Finset.card_eq_two.mp hs).choose (Finset.card_eq_two.mp hs).choose_spec.choose
  else 0

theorem edgeVertex_eq_pair (s : Finset Coord) (hs : s.card = 2) :
    ∃ i j : Coord, i ≠ j ∧ s = {i,j} ∧ edgeVertex s = pair i j := by
  let h := Finset.card_eq_two.mp hs
  exact ⟨h.choose,h.choose_spec.choose,h.choose_spec.choose_spec.1,
    h.choose_spec.choose_spec.2,by simp only [edgeVertex,dif_pos hs]⟩

theorem edgeVertex_pair (i j : Coord) (hij : i ≠ j) :
    edgeVertex {i,j} = pair i j := by
  obtain ⟨k,l,hkl,he,hv⟩ := edgeVertex_eq_pair {i,j} (by simp [hij])
  rcases (SquareIncidence.pair_support_eq_iff i j k l hij hkl).mp he with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact hv
  · exact hv.trans (pair_comm _ _)

theorem pair_bit_true_iff (i j k : Coord) (hij : i ≠ j) :
    (pair i j).val.testBit k.val = true ↔ k=i ∨ k=j := by
  by_cases hki : k=i
  · subst k
    simp [bit_pair,hij,Ne.symm hij]
  by_cases hkj : k=j
  · subst k
    simp [bit_pair,hij,Ne.symm hij]
  simp [bit_pair,hki,hkj,Ne.symm hki,Ne.symm hkj]

theorem pair_vertex_eq_support (i j k l : Coord) (hij : i ≠ j) (hkl : k ≠ l)
    (he : pair i j = pair k l) : ({i,j} : Finset Coord) = {k,l} := by
  apply Finset.ext
  intro x
  have hb := congrArg (fun v : Vertex => v.val.testBit x.val) he
  simpa only [Finset.mem_insert,Finset.mem_singleton] using
    (pair_bit_true_iff i j x hij).symm.trans ((congrArg (fun b => b=true) hb).to_iff.trans (pair_bit_true_iff k l x hkl))

theorem edgeVertex_injective_on_pairs (s t : Finset Coord) (hs : s.card = 2)
    (ht : t.card = 2) (he : edgeVertex s = edgeVertex t) : s=t := by
  obtain ⟨i,j,hij,rfl,hi⟩ := edgeVertex_eq_pair s hs
  obtain ⟨k,l,hkl,rfl,hk⟩ := edgeVertex_eq_pair t ht
  exact pair_vertex_eq_support i j k l hij hkl (hi.symm.trans (he.trans hk))

#print axioms selectedEndpoints_card
#print axioms two_endpoint_images_card
#print axioms five_not_covered_by_two_endpoints
#print axioms edgeVertex_injective_on_pairs
end
end Snake9
