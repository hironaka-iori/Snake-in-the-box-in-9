import MixedIsolatedEndpoints
import TwoEdgeEndpointDemand

namespace Snake9
open Finset Classical
noncomputable section
set_option maxHeartbeats 2400000

def OrdinaryEdgeEndpointMember (a b c d e : Coord) (s : Finset Coord) (v : Vertex) : Prop :=
  v=edgeVertex s ∨ ∃k∈distinctR a b c d,k≠e ∧ s={e,k} ∧ v=pair b k

theorem ordinary_endpoint_other_bit (a b c d e k : Coord) (s : Finset Coord)
    (hs : s.card=2) (hk : k∈distinctR a b c d) (hks : k∉s)
    (v : Vertex) (hv : OrdinaryEdgeEndpointMember a b c d e s v) : v.val.testBit k.val=false := by
  rcases hv with rfl | ⟨r,hr,hre,he,rfl⟩
  · obtain ⟨i,j,hij,rfl,hv⟩ := edgeVertex_eq_pair s hs
    have hki : k≠i := by intro he; exact hks (by simp [he])
    have hkj : k≠j := by intro he; exact hks (by simp [he])
    rw [hv]
    simp [bit_pair,Ne.symm hki,Ne.symm hkj]
  · have hkr : k≠r := by intro hh; exact hks (by rw [he,hh]; simp)
    have hkb := ((mem_distinctR a b c d k).mp hk).2.1
    simp [bit_pair,Ne.symm hkb,Ne.symm hkr]

theorem ordinary_endpoint_injective (a b c d e : Coord) (s t : Finset Coord)
    (hs : s.card=2) (ht : t.card=2) (hsR : s⊆distinctR a b c d) (htR : t⊆distinctR a b c d)
    (v w : Vertex) (hv : OrdinaryEdgeEndpointMember a b c d e s v)
    (hw : OrdinaryEdgeEndpointMember a b c d e t w) (he : v=w) : s=t := by
  have neq (u : Finset Coord) (hu : u.card=2) (huR : u⊆distinctR a b c d)
      (k : Coord) (hk : k∈distinctR a b c d) : edgeVertex u≠pair b k := by
    obtain ⟨i,j,hij,rfl,hv⟩ := edgeVertex_eq_pair u hu
    have hib := ((mem_distinctR a b c d i).mp (huR (by simp))).2.1
    have hjb := ((mem_distinctR a b c d j).mp (huR (by simp))).2.1
    have hkb := ((mem_distinctR a b c d k).mp hk).2.1
    rw [hv]
    intro hh
    have hb := congrArg (fun z : Vertex => z.val.testBit b.val) hh
    simp [bit_pair,hib,hjb,hkb] at hb
  rcases hv with rfl | ⟨k,hk,hke,hsk,rfl⟩
  · rcases hw with rfl | ⟨l,hl,hle,htl,rfl⟩
    · exact edgeVertex_injective_on_pairs s t hs ht he
    · exact False.elim (neq s hs hsR l hl he)
  · rcases hw with rfl | ⟨l,hl,hle,htl,rfl⟩
    · exact False.elim (neq t ht htR k hk he.symm)
    · have hkl : k=l := pair_injective_right b k l he
      rw [hsk,htl,hkl]

theorem isolated_ordinary_resource_count {m : Nat} (p : Snake m) (a b c d e : Coord)
    (F : Finset (Finset Coord)) (hedge : ∀s∈F,s.card=2)
    (hep : ∀k∈distinctR a b c d,PairIsolated F k →
      ∃v,InPath p v ∧ AtMostOneNeighbor p v ∧ ActiveEndpointMember a b c d k v)
    (heprr : ∀s∈F,s⊆distinctR a b c d →
      ∃v,InPath p v ∧ AtMostOneNeighbor p v ∧ OrdinaryEdgeEndpointMember a b c d e s v) :
    (starIsolatedIndices (distinctR a b c d) F).card+
      (starOrdinaryEdges (distinctR a b c d) F).card≤2 := by
  let I := starIsolatedIndices (distinctR a b c d) F
  let J := starOrdinaryEdges (distinctR a b c d) F
  have hi (k : Coord) (hk : k∈I) : k∈distinctR a b c d ∧ PairIsolated F k := by
    obtain ⟨hkR,hkF⟩ := Finset.mem_sdiff.mp hk
    exact ⟨hkR,fun s hs hks => hkF (Finset.mem_biUnion.mpr ⟨s,hs,hks⟩)⟩
  have hj (s : Finset Coord) (hs : s∈J) : s∈F ∧ s⊆distinctR a b c d := Finset.mem_filter.mp hs
  have hex : ∀k : Coord,∃v : Vertex,k∈I →
      InPath p v ∧ AtMostOneNeighbor p v ∧ ActiveEndpointMember a b c d k v := by
    intro k
    by_cases hk : k∈I
    · obtain ⟨v,hv⟩ := hep k (hi k hk).1 (hi k hk).2
      exact ⟨v,fun _ => hv⟩
    · exact ⟨0,fun hk' => False.elim (hk hk')⟩
  choose g hg using hex
  have hex' : ∀s : Finset Coord,∃v : Vertex,s∈J →
      InPath p v ∧ AtMostOneNeighbor p v ∧ OrdinaryEdgeEndpointMember a b c d e s v := by
    intro s
    by_cases hs : s∈J
    · obtain ⟨v,hv⟩ := heprr s (hj s hs).1 (hj s hs).2
      exact ⟨v,fun _ => hv⟩
    · exact ⟨0,fun hs' => False.elim (hs hs')⟩
  choose q hq using hex'
  have hgi : Set.InjOn g I := by
    intro k hk l hl he
    by_contra hkl
    exact active_endpoint_groups_disjoint a b c d k l (hi k hk).1 hkl _ _
      (hg k hk).2.2 (hg l hl).2.2 he
  have hqi : Set.InjOn q J := by
    intro s hs t ht he
    exact ordinary_endpoint_injective a b c d e s t (hedge s (hj s hs).1) (hedge t (hj t ht).1)
      (hj s hs).2 (hj t ht).2 _ _ (hq s hs).2.2 (hq t ht).2.2 he
  have hdis : ∀k∈I,∀s∈J,g k≠q s := by
    intro k hk s hs he
    have hb := congrArg (fun v : Vertex => v.val.testBit k.val) he
    dsimp only at hb
    rw [active_endpoint_bit a b c d k (hi k hk).1 _ (hg k hk).2.2,
      ordinary_endpoint_other_bit a b c d e k s (hedge s (hj s hs).1)
        (hi k hk).1 ((hi k hk).2 s (hj s hs).1) _ (hq s hs).2.2] at hb
    contradiction
  exact two_endpoint_images_card p I J g q hgi hqi
    (fun k hk => ⟨(hg k hk).1,(hg k hk).2.1⟩)
    (fun s hs => ⟨(hq s hs).1,(hq s hs).2.1⟩) hdis

#print axioms isolated_ordinary_resource_count
end
end Snake9
