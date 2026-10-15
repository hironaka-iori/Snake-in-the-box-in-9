import OrdinaryIsolatedOneSide
import OrdinaryPairEndpoints
import OrdinaryOuterHoleEndpoints
import OrdinaryHoleResources
import FourEndpointCounting

namespace Snake9
open Finset Classical
noncomputable section
set_option maxHeartbeats 2600000
namespace OrdinaryOuterConfig
variable {m : Nat} {p : Snake m} {a b c d : Coord} (h : OrdinaryOuterConfig p a b c d)
include h

theorem endpoint_demand_bound (f : MissingAtNeighbor p a b) :
    ordinaryEndpointDemand f.F (distinctR a b c d) h.A h.B c d≤2 := by
  let R := distinctR a b c d
  let I := ordinaryGoodIndices f.F R h.A h.B c d
  let L := f.F.filter (fun s => s⊆R ∧ Disjoint s h.A)
  let Q := f.F.filter (fun s => s⊆R ∧ Disjoint s h.B)
  let P := OrdinaryHoleGood f.F R c d h.A h.B
  let P' := OrdinaryHoleGood f.F R c d h.B h.A
  let U := ordinaryHoleVertex a h.A
  let V := ordinaryHoleVertex a h.B
  let H : Finset Vertex := (if P then {U} else ∅)∪(if P' then {V} else ∅)
  have hi (k : Coord) (hk : k∈I) : k∈R ∧ OrdinaryGoodRow f.F R h.A h.B c d k := Finset.mem_filter.mp hk
  have hl (s : Finset Coord) (hs : s∈L) : s∈f.F ∧ s⊆R ∧ Disjoint s h.A := Finset.mem_filter.mp hs
  have hq (s : Finset Coord) (hs : s∈Q) : s∈f.F ∧ s⊆R ∧ Disjoint s h.B := Finset.mem_filter.mp hs
  have hex : ∀k : Coord,∃v : Vertex,k∈I →
      InPath p v ∧ AtMostOneNeighbor p v ∧ ActiveEndpointMember a b c d k v := by
    intro k
    by_cases hk : k∈I
    · obtain ⟨v,hv⟩ := h.good_row_endpoint f k (hi k hk).1 (hi k hk).2
      exact ⟨v,fun _ => hv⟩
    · exact ⟨0,fun hk' => False.elim (hk hk')⟩
  choose g hg using hex
  let q : Finset Coord → Vertex := fun s => vxor (pair a b) (edgeVertex s)
  have qp (i j : Coord) (hij : i≠j) : q {i,j}=quad a b i j := by
    simp only [q,edgeVertex_pair i j hij,quad,triple,pair,vxor_assoc]
  have hgi : Set.InjOn g I := by
    intro k hk l hl' he
    by_contra hkl
    exact active_endpoint_groups_disjoint a b c d k l (hi k hk).1 hkl _ _ (hg k hk).2.2 (hg l hl').2.2 he
  have hli : Set.InjOn edgeVertex L := by
    intro s hs t ht he
    exact edgeVertex_injective_on_pairs s t (f.edge_card s (hl s hs).1) (f.edge_card t (hl t ht).1) he
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
    have hiA : i∉h.A := fun hm => Finset.disjoint_left.mp hh.2.2 (by simp) hm
    have hjA : j∉h.A := fun hm => Finset.disjoint_left.mp hh.2.2 (by simp) hm
    rw [hv]
    exact ⟨h.left_clean_pair i j hir hjr hij hiA,h.missing_ordinary_pair_low f i j hir hjr hij hiA hjA hh.1⟩
  have hqs : ∀s∈Q,InPath p (q s) ∧ AtMostOneNeighbor p (q s) := by
    intro s hs
    have hh := hq s hs
    obtain ⟨i,j,hij,rfl⟩ := Finset.card_eq_two.mp (f.edge_card s hh.1)
    have hir := hh.2.1 (by simp : i∈({i,j}:Finset Coord))
    have hjr := hh.2.1 (by simp : j∈({i,j}:Finset Coord))
    have hiB : i∉h.B := fun hm => Finset.disjoint_left.mp hh.2.2 (by simp) hm
    have hjB : j∉h.B := fun hm => Finset.disjoint_left.mp hh.2.2 (by simp) hm
    have hne : ({i,j}:Finset Coord)≠h.B := fun he => hiB (he ▸ (by simp : i∈({i,j}:Finset Coord)))
    rw [qp i j hij]
    exact ⟨(h.right_pair_iff i j hir hjr hij).mpr hne,h.missing_ordinary_quad_low f i j hir hjr hij hiB hjB hh.1⟩
  have hUs : P → InPath p U ∧ AtMostOneNeighbor p U := by
    intro hp
    obtain ⟨i,j,hij,hA⟩ := Finset.card_eq_two.mp h.Acard
    have he : U=triple a i j := by simp only [U,ordinaryHoleVertex,hA,edgeVertex_pair i j hij,triple,pair,vxor_assoc]
    rw [he]
    exact h.left_hole_endpoint f i j hij hA.symm hp
  have hVs : P' → InPath p V ∧ AtMostOneNeighbor p V := by
    intro hp
    obtain ⟨i,j,hij,hB⟩ := Finset.card_eq_two.mp h.Bcard
    have he : V=triple a i j := by simp only [V,ordinaryHoleVertex,hB,edgeVertex_pair i j hij,triple,pair,vxor_assoc]
    rw [he]
    exact h.right_hole_endpoint f i j hij hB.symm hp
  have hHmem (v : Vertex) (hv : v∈H) : (v=U ∧ P) ∨ (v=V ∧ P') := by
    simp only [H,Finset.mem_union] at hv
    rcases hv with hv | hv
    · by_cases hp : P
      · exact Or.inl ⟨by simpa only [if_pos hp,Finset.mem_singleton] using hv,hp⟩
      · simp [hp] at hv
    · by_cases hp : P'
      · exact Or.inr ⟨by simpa only [if_pos hp,Finset.mem_singleton] using hv,hp⟩
      · simp [hp] at hv
  have hHs : ∀v∈H,InPath p v ∧ AtMostOneNeighbor p v := by
    intro v hv
    rcases hHmem v hv with ⟨rfl,hp⟩ | ⟨rfl,hp⟩
    · exact hUs hp
    · exact hVs hp
  have gnotpair (k : Coord) (hk : k∈I) (s : Finset Coord) (hs : s∈L) : g k≠edgeVertex s := by
    intro he
    have hh := hl s hs
    obtain ⟨i,j,hij,rfl,hv⟩ := edgeVertex_eq_pair s (f.edge_card s hh.1)
    have hki : k≠i := by intro he; exact (hi k hk).2.1 _ hh.1 (by simp [he])
    have hkj : k≠j := by intro he; exact (hi k hk).2.1 _ hh.1 (by simp [he])
    have hb := active_endpoint_bit a b c d k (hi k hk).1 _ (hg k hk).2.2
    rw [he,hv] at hb
    simp [bit_pair,Ne.symm hki,Ne.symm hkj] at hb
  have gnotquad (k : Coord) (hk : k∈I) (s : Finset Coord) (hs : s∈Q) : g k≠q s := by
    intro he
    have hh := hq s hs
    obtain ⟨i,j,hij,rfl⟩ := Finset.card_eq_two.mp (f.edge_card s hh.1)
    have hki : k≠i := by intro he; exact (hi k hk).2.1 _ hh.1 (by simp [he])
    have hkj : k≠j := by intro he; exact (hi k hk).2.1 _ hh.1 (by simp [he])
    have hk' := (mem_distinctR a b c d k).mp (hi k hk).1
    have hb := active_endpoint_bit a b c d k (hi k hk).1 _ (hg k hk).2.2
    rw [he,qp i j hij] at hb
    simp [bit_quad,Ne.symm hk'.1,Ne.symm hk'.2.1,Ne.symm hki,Ne.symm hkj] at hb
  have pairbit (s : Finset Coord) (hs : s∈L) : (edgeVertex s).val.testBit a.val=false := by
    have hh := hl s hs
    obtain ⟨i,j,hij,rfl,hv⟩ := edgeVertex_eq_pair s (f.edge_card s hh.1)
    have hia := ((mem_distinctR a b c d i).mp (hh.2.1 (by simp))).1
    have hja := ((mem_distinctR a b c d j).mp (hh.2.1 (by simp))).1
    rw [hv]
    simp [bit_pair,hia,hja]
  have quadbits (s : Finset Coord) (hs : s∈Q) :
      (q s).val.testBit a.val=true ∧ (q s).val.testBit b.val=true := by
    have hh := hq s hs
    obtain ⟨i,j,hij,rfl⟩ := Finset.card_eq_two.mp (f.edge_card s hh.1)
    have hi' := (mem_distinctR a b c d i).mp (hh.2.1 (by simp))
    have hj' := (mem_distinctR a b c d j).mp (hh.2.1 (by simp))
    rw [qp i j hij]
    simp [bit_quad,h.outer.hab,Ne.symm h.outer.hab,hi'.1,hj'.1,hi'.2.1,hj'.2.1]
  have hUb := ordinaryHoleVertex_bits h.outer h.A h.Acard h.Asub
  have hVb := ordinaryHoleVertex_bits h.outer h.B h.Bcard h.Bsub
  have hUV : U≠V := fun he => h.hne (ordinaryHoleVertex_injective a h.A h.B h.Acard h.Bcard he)
  have hHcard : H.card=(if P then 1 else 0)+(if P' then 1 else 0) := by
    have he : ({U}:Finset Vertex)∪{V}={U,V} := by ext x; simp
    by_cases hp : P <;> by_cases hp' : P' <;> simp [H,hp,hp',he,hUV]
  have hpairquad : ∀s∈L,∀t∈Q,edgeVertex s≠q t := by
    intro s hs t ht he
    have hb := congrArg (fun v : Vertex => v.val.testBit a.val) he
    dsimp only at hb
    rw [pairbit s hs,(quadbits t ht).1] at hb
    contradiction
  have hpairH : ∀s∈L,∀v∈H,edgeVertex s≠v := by
    intro s hs v hv he
    have hb := congrArg (fun v : Vertex => v.val.testBit a.val) he
    dsimp only at hb
    rw [pairbit s hs] at hb
    rcases hHmem v hv with ⟨rfl,hp⟩ | ⟨rfl,hp⟩
    · exact Bool.false_ne_true (hb.trans hUb.1)
    · exact Bool.false_ne_true (hb.trans hVb.1)
  have hquadH : ∀s∈Q,∀v∈H,q s≠v := by
    intro s hs v hv he
    have hb := congrArg (fun v : Vertex => v.val.testBit b.val) he
    dsimp only at hb
    rw [(quadbits s hs).2] at hb
    rcases hHmem v hv with ⟨rfl,hp⟩ | ⟨rfl,hp⟩
    · exact Bool.noConfusion (hb.trans hUb.2.1)
    · exact Bool.noConfusion (hb.trans hVb.2.1)
  have hgH : ∀k∈I,∀v∈H,g k≠v := by
    intro k hk v hv
    rcases hHmem v hv with ⟨rfl,hp⟩ | ⟨rfl,hp⟩
    · exact active_ne_ordinaryHoleVertex h.outer h.A h.Acard h.Asub k (hi k hk).1 _ (hg k hk).2.2
    · exact active_ne_ordinaryHoleVertex h.outer h.B h.Bcard h.Bsub k (hi k hk).1 _ (hg k hk).2.2
  have dis_images {α β : Type} [DecidableEq α] [DecidableEq β]
      (S : Finset α) (T : Finset β) (u : α → Vertex) (v : β → Vertex)
      (hne : ∀s∈S,∀t∈T,u s≠v t) : Disjoint (S.image u) (T.image v) := by
    apply Finset.disjoint_left.mpr
    intro w hw hw'
    obtain ⟨s,hs,he⟩ := Finset.mem_image.mp hw
    obtain ⟨t,ht,he'⟩ := Finset.mem_image.mp hw'
    exact hne s hs t ht (he.trans he'.symm)
  have dis_H {α : Type} [DecidableEq α] (S : Finset α) (u : α → Vertex)
      (hne : ∀s∈S,∀v∈H,u s≠v) : Disjoint (S.image u) H := by
    apply Finset.disjoint_left.mpr
    intro w hw hw'
    obtain ⟨s,hs,he⟩ := Finset.mem_image.mp hw
    exact hne s hs w hw' he
  have hb := four_endpoint_finsets_card p (I.image g) (L.image edgeVertex) (Q.image q) H
    (by intro v hv; obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hv; exact ⟨(hg k hk).1,(hg k hk).2.1⟩)
    (by intro v hv; obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hv; exact hls s hs)
    (by intro v hv; obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hv; exact hqs s hs)
    hHs (dis_images I L g edgeVertex gnotpair) (dis_images I Q g q gnotquad) (dis_H I g hgH)
    (dis_images L Q edgeVertex q hpairquad) (dis_H L edgeVertex hpairH) (dis_H Q q hquadH)
  rw [Finset.card_image_of_injOn hgi,Finset.card_image_of_injOn hli,
    Finset.card_image_of_injOn hqi,hHcard] at hb
  change I.card+L.card+Q.card+(if P then 1 else 0)+(if P' then 1 else 0)≤2
  omega

end OrdinaryOuterConfig
#print axioms OrdinaryOuterConfig.endpoint_demand_bound
end
end Snake9
