import ThreeEndpointCounting
import StarOuterCounting
import StarOuterResidual

namespace Snake9
open Finset Classical
noncomputable section
set_option maxHeartbeats 2400000

namespace StarOuterConfig
variable {m : Nat} {p : Snake m} {a b c d : Coord} (h : StarOuterConfig p a b c d)
include h

theorem endpoint_resource_count (f : MissingAtNeighbor p a b) :
    starEndpointCount (distinctR a b c d) f.F h.e h.f≤2 := by
  let R := distinctR a b c d
  let I := starIsolatedIndices R f.F
  let L := (starOrdinaryEdges R f.F).filter (fun s => h.e∉s)
  let Q := (starOrdinaryEdges R f.F).filter (fun s => h.f∉s)
  have hi (k : Coord) (hk : k∈I) : k∈R ∧ ∀s∈f.F,k∉s := by
    obtain ⟨hkr,hkn⟩ := Finset.mem_sdiff.mp hk
    exact ⟨hkr,fun s hs hks => hkn (Finset.mem_biUnion.mpr ⟨s,hs,hks⟩)⟩
  have hl (s : Finset Coord) (hs : s∈L) : s∈f.F ∧ s⊆R ∧ h.e∉s := by
    obtain ⟨hs,he⟩ := Finset.mem_filter.mp hs
    obtain ⟨hf,hr⟩ := Finset.mem_filter.mp hs
    exact ⟨hf,hr,he⟩
  have hq (s : Finset Coord) (hs : s∈Q) : s∈f.F ∧ s⊆R ∧ h.f∉s := by
    obtain ⟨hs,he⟩ := Finset.mem_filter.mp hs
    obtain ⟨hf,hr⟩ := Finset.mem_filter.mp hs
    exact ⟨hf,hr,he⟩
  have hex : ∀k : Coord,∃v : Vertex,k∈I →
      InPath p v ∧ AtMostOneNeighbor p v ∧ DenseRowResource a b c d k v := by
    intro k
    by_cases hk : k∈I
    · obtain ⟨v,hv⟩ := h.isolated_endpoint f k (hi k hk).1 (hi k hk).2
      exact ⟨v,fun _ => hv⟩
    · exact ⟨0,fun hki => False.elim (hk hki)⟩
  choose g hg using hex
  let q : Finset Coord → Vertex := fun s => vxor (pair a b) (edgeVertex s)
  have qp (i j : Coord) (hij : i≠j) : q {i,j}=quad a b i j := by
    simp only [q,edgeVertex_pair i j hij,quad,triple,pair,vxor_assoc]
  have hgi : Set.InjOn g I := by
    intro k hk l hl' he
    by_contra hkl
    have hb := congrArg (fun v : Vertex => v.val.testBit k.val) he
    dsimp only at hb
    rw [h.resource_bit_self k (hi k hk).1 _ (hg k hk).2.2,
      h.resource_bit_other l k (hi k hk).1 (Ne.symm hkl) _ (hg l hl').2.2] at hb
    contradiction
  have hli : Set.InjOn edgeVertex L := by
    intro s hs t ht he
    exact edgeVertex_injective_on_pairs s t (f.edge_card s (hl s hs).1)
      (f.edge_card t (hl t ht).1) he
  have hqi : Set.InjOn q Q := by
    intro s hs t ht he
    apply edgeVertex_injective_on_pairs s t (f.edge_card s (hq s hs).1) (f.edge_card t (hq t ht).1)
    have hh := congrArg (vxor (pair a b)) he
    simpa only [q,vxor_cancel] using hh
  have hls : ∀s∈L,InPath p (edgeVertex s) ∧ AtMostOneNeighbor p (edgeVertex s) := by
    intro s hs
    have hh := hl s hs
    obtain ⟨i,j,hij,rfl,hv⟩ := edgeVertex_eq_pair s (f.edge_card s hh.1)
    have hir := hh.2.1 (by simp : i∈({i,j}:Finset Coord))
    have hjr := hh.2.1 (by simp : j∈({i,j}:Finset Coord))
    have hie : i≠h.e := by intro he; exact hh.2.2 (by simp [←he])
    have hje : j≠h.e := by intro he; exact hh.2.2 (by simp [←he])
    rw [hv]
    exact ⟨(h.ordinary_corners i j hir hjr hij).1,h.missing_pair_low f i j hir hjr hij hie hje hh.1⟩
  have hqs : ∀s∈Q,InPath p (q s) ∧ AtMostOneNeighbor p (q s) := by
    intro s hs
    have hh := hq s hs
    obtain ⟨i,j,hij,rfl⟩ := Finset.card_eq_two.mp (f.edge_card s hh.1)
    have hir := hh.2.1 (by simp : i∈({i,j}:Finset Coord))
    have hjr := hh.2.1 (by simp : j∈({i,j}:Finset Coord))
    have hif : i≠h.f := by intro he; exact hh.2.2 (by simp [←he])
    have hjf : j≠h.f := by intro he; exact hh.2.2 (by simp [←he])
    rw [qp i j hij]
    exact ⟨(h.ordinary_corners i j hir hjr hij).2,h.missing_quad_low f i j hir hjr hij hif hjf hh.1⟩
  have hgl : ∀k∈I,∀s∈L,g k≠edgeVertex s := by
    intro k hk s hs he
    have hh := hl s hs
    obtain ⟨i,j,hij,rfl,hv⟩ := edgeVertex_eq_pair s (f.edge_card s hh.1)
    have hki : k≠i := by intro he; exact (hi k hk).2 _ hh.1 (by simp [he])
    have hkj : k≠j := by intro he; exact (hi k hk).2 _ hh.1 (by simp [he])
    have hb := h.resource_bit_self k (hi k hk).1 _ (hg k hk).2.2
    rw [he,hv] at hb
    simp [bit_pair,Ne.symm hki,Ne.symm hkj] at hb
  have hgq : ∀k∈I,∀s∈Q,g k≠q s := by
    intro k hk s hs he
    have hh := hq s hs
    obtain ⟨i,j,hij,rfl⟩ := Finset.card_eq_two.mp (f.edge_card s hh.1)
    have hki : k≠i := by intro he; exact (hi k hk).2 _ hh.1 (by simp [he])
    have hkj : k≠j := by intro he; exact (hi k hk).2 _ hh.1 (by simp [he])
    have hk' := (mem_distinctR a b c d k).mp (hi k hk).1
    have hb := h.resource_bit_self k (hi k hk).1 _ (hg k hk).2.2
    rw [he,qp i j hij] at hb
    simp [bit_quad,Ne.symm hk'.1,Ne.symm hk'.2.1,Ne.symm hki,Ne.symm hkj] at hb
  have hlq : ∀s∈L,∀t∈Q,edgeVertex s≠q t := by
    intro s hs t ht he
    have hh := hl s hs
    have hh' := hq t ht
    obtain ⟨i,j,hij,rfl,hv⟩ := edgeVertex_eq_pair s (f.edge_card s hh.1)
    obtain ⟨k,l,hkl,rfl⟩ := Finset.card_eq_two.mp (f.edge_card t hh'.1)
    have hia := ((mem_distinctR a b c d i).mp (hh.2.1 (by simp))).1
    have hja := ((mem_distinctR a b c d j).mp (hh.2.1 (by simp))).1
    have hka := ((mem_distinctR a b c d k).mp (hh'.2.1 (by simp))).1
    have hla := ((mem_distinctR a b c d l).mp (hh'.2.1 (by simp))).1
    rw [hv,qp k l hkl] at he
    have hb := congrArg (fun v : Vertex => v.val.testBit a.val) he
    simp [bit_pair,bit_quad,Ne.symm h.outer.hab,hia,hja,hka,hla] at hb
  exact three_endpoint_images_card p I L Q g edgeVertex q hgi hli hqi
    (fun k hk => ⟨(hg k hk).1,(hg k hk).2.1⟩) hls hqs hgl hgq hlq

end StarOuterConfig
#print axioms StarOuterConfig.endpoint_resource_count
end
end Snake9
