import DistinctOuterFamilies
import DistinctOuterCounting

namespace Snake9
open Finset Classical
noncomputable section
set_option maxHeartbeats 2000000

theorem selected_has_neighbor_of_nontrivial {m : Nat} (p : Snake m) (hm : 1≤m)
    (v : Vertex) (hv : InPath p v) : ∃w,InPath p w ∧ Adj v w := by
  obtain ⟨i,rfl⟩ := hv
  by_cases hi : i.val=0
  · let j : Fin (m+1) := ⟨1,by omega⟩
    exact ⟨p.vertex j,⟨j,rfl⟩,(path_adj_iff p i j).mpr (Or.inl (by dsimp [j]; omega))⟩
  · let j : Fin (m+1) := ⟨i.val-1,by have hb := i.isLt; omega⟩
    exact ⟨p.vertex j,⟨j,rfl⟩,(path_adj_iff p i j).mpr (Or.inr (by dsimp [j]; omega))⟩

namespace DistinctOuterConfig
variable {m : Nat} {p : Snake m} {a b c d : Coord} (h : DistinctOuterConfig p a b c d)
include h

theorem nontrivial : 1≤m := by
  obtain ⟨i,hi⟩ := h.hzero
  obtain ⟨j,hj⟩ := h.ha
  have hadj : Adj (p.vertex i) (p.vertex j) := by rw [hi,hj]; exact (adj_zero_iff _).mpr ⟨a,rfl⟩
  have hh := (path_adj_iff p i j).mp hadj
  have hbi := i.isLt
  have hbj := j.isLt
  omega

theorem row_connection_resource (B : Finset Coord) (hHB : h.holes⊆B)
    (k l : Coord) (hk : k∈distinctR a b c d\h.holes) (hl : l∈distinctR a b c d)
    (hkl : k≠l) (hkB : k∉B) (hconn : InPath p (triple b k l)) :
    k∈outerEdgeResources B h.leftRemainder h.rightRemainder := by
  obtain ⟨hka,hkb,hkc,hkd⟩ := (mem_distinctR a b c d k).mp (Finset.mem_sdiff.mp hk).1
  obtain ⟨hla,hlb,hlc,hld⟩ := (mem_distinctR a b c d l).mp hl
  have hh := h.row_connection_missing k l (Finset.mem_sdiff.mp hk).1 hl hkl (h.selected_row k hk) hconn
  by_cases hlH : l∈h.holes
  · apply mem_outerEdgeResources B h.leftRemainder h.rightRemainder k l hkB
    apply Or.inl
    refine ⟨hHB hlH,?_⟩
    rcases hh.1 with he | he
    · exact Finset.mem_union_left _ (h.leftRemainder_pair k l hkb hlb he)
    · exact Finset.mem_union_right _ (h.rightRemainder_pair k l hka hla he)
  · obtain ⟨hleft,hright⟩ := hh.2 (h.selected_row l (Finset.mem_sdiff.mpr ⟨hl,hlH⟩))
    apply Finset.mem_union_left
    apply Finset.mem_union_left
    exact Finset.mem_biUnion.mpr ⟨{k,l},Finset.mem_inter.mpr
      ⟨h.leftRemainder_pair k l hkb hlb hleft,h.rightRemainder_pair k l hka hla hright⟩,by simp⟩

theorem c_connection_resource (B : Finset Coord) (hcB : c∈B)
    (hac : ({a,c}:Finset Coord)∉h.right.F)
    (k : Coord) (hk : k∈distinctR a b c d\h.holes) (hkB : k∉B)
    (hconn : InPath p (triple b k c)) :
    k∈outerEdgeResources B h.leftRemainder h.rightRemainder := by
  obtain ⟨hka,hkb,hkc,hkd⟩ := (mem_distinctR a b c d k).mp (Finset.mem_sdiff.mp hk).1
  have he := (h.c_connection_missing k (Finset.mem_sdiff.mp hk).1 (h.selected_row k hk) hconn).resolve_left hac
  have hm := h.rightRemainder_pair c k (Ne.symm h.hac) hka he
  rw [Finset.pair_comm c k] at hm
  exact mem_outerEdgeResources B _ _ k c hkB (Or.inl ⟨hcB,Finset.mem_union_right _ hm⟩)

theorem d_connection_resource (B : Finset Coord) (hdB : d∈B)
    (hbd : ({b,d}:Finset Coord)∉h.left.F)
    (k : Coord) (hk : k∈distinctR a b c d\h.holes) (hkB : k∉B)
    (hconn : InPath p (triple b k d)) :
    k∈outerEdgeResources B h.leftRemainder h.rightRemainder := by
  obtain ⟨hka,hkb,hkc,hkd⟩ := (mem_distinctR a b c d k).mp (Finset.mem_sdiff.mp hk).1
  have he := (h.d_connection_missing k (Finset.mem_sdiff.mp hk).1 (h.selected_row k hk) hconn).resolve_left hbd
  have hm := h.leftRemainder_pair d k (Ne.symm h.hbd) hkb he
  rw [Finset.pair_comm d k] at hm
  exact mem_outerEdgeResources B _ _ k d hkB (Or.inl ⟨hdB,Finset.mem_union_left _ hm⟩)

theorem zero_delta_impossible (hbd : ({b,d}:Finset Coord)∉h.left.F)
    (hac : ({a,c}:Finset Coord)∉h.right.F) : False := by
  apply outer_zero_delta_count_false (distinctR a b c d) h.holes h.leftRemainder h.rightRemainder c d
  · simp [distinctR,Finset.card_sdiff (Finset.subset_univ _),Coord,h.hab,h.hac,h.had,h.hbc,h.hbd,h.hcd]
  · exact h.holes_subset
  · exact h.left_count_absent hbd
  · exact h.right_count_absent hac
  · exact h.leftRemainder_edge_card
  · exact h.rightRemainder_edge_card
  · intro k hk
    have hr := (Finset.mem_sdiff.mp hk).1
    obtain ⟨hka,hkb,hkc,hkd⟩ := (mem_distinctR a b c d k).mp hr
    have hkB : k∉h.holes∪({c,d}:Finset Coord) := by simp [(Finset.mem_sdiff.mp hk).2,hkc,hkd]
    obtain ⟨w,hw,hadj⟩ := selected_has_neighbor_of_nontrivial p h.nontrivial _ (h.selected_row k hk)
    rcases h.row_neighbor_cover k hr w hw hadj with he | he | ⟨l,hl,hlk,rfl⟩
    · rw [he] at hw
      exact h.c_connection_resource _ (by simp) hac k hk hkB hw
    · rw [he] at hw
      exact h.d_connection_resource _ (by simp) hbd k hk hkB hw
    · exact h.row_connection_resource _ (Finset.subset_union_left) k l hk hl (Ne.symm hlk) hkB hw

def rowEndpoints : Finset Coord := (distinctR a b c d\h.holes).filter (fun k => AtMostOneNeighbor p (pair b k))

theorem rowEndpoints_card : h.rowEndpoints.card≤2 := by
  have hs : h.rowEndpoints.image (fun k => pair b k)⊆selectedEndpoints p := by
    intro v hv
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨hk,hlo⟩ := Finset.mem_filter.mp hk
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,h.selected_row k hk,hlo⟩
  have hc := (Finset.card_le_card hs).trans (selectedEndpoints_card p)
  have hinj : Set.InjOn (fun k => pair b k) h.rowEndpoints := by
    intro k hk l hl he
    exact pair_injective_right b k l he
  rwa [Finset.card_image_of_injOn hinj] at hc

theorem one_delta_resource_cover (hac : ({a,c}:Finset Coord)∉h.right.F) :
    distinctR a b c d\h.holes ⊆ h.rowEndpoints ∪
      outerEdgeResources (h.holes∪{c}) h.leftRemainder h.rightRemainder := by
  intro k hk
  by_cases hlo : AtMostOneNeighbor p (pair b k)
  · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hk,hlo⟩)
  apply Finset.mem_union_right
  have hr := (Finset.mem_sdiff.mp hk).1
  obtain ⟨hka,hkb,hkc,hkd⟩ := (mem_distinctR a b c d k).mp hr
  have hkB : k∉h.holes∪({c}:Finset Coord) := by simp [(Finset.mem_sdiff.mp hk).2,hkc]
  obtain ⟨w,hw,hadj,hwn⟩ := neighbor_other_of_not_low p (pair b k) (triple b k d) hlo
  rcases h.row_neighbor_cover k hr w hw hadj with he | he | ⟨l,hl,hlk,rfl⟩
  · rw [he] at hw
    exact h.c_connection_resource _ (by simp) hac k hk hkB hw
  · exact False.elim (hwn he)
  · exact h.row_connection_resource _ (Finset.subset_union_left) k l hk hl (Ne.symm hlk) hkB hw

theorem one_delta_remainder_shape (hbd : ({b,d}:Finset Coord)∈h.left.F)
    (hac : ({a,c}:Finset Coord)∉h.right.F) :
    h.holes=∅ ∧ ∃i j k : Coord,
      i∈distinctR a b c d ∧ j∈distinctR a b c d ∧ k∈distinctR a b c d ∧
      i≠j ∧ i≠k ∧ j≠k ∧ h.leftRemainder={{i,j}} ∧ h.rightRemainder={{i,j},{c,k}} := by
  have hc := h.left_count_present hbd
  obtain ⟨hH,hG,hJ,hC⟩ := outer_one_delta_count (distinctR a b c d) h.holes h.rowEndpoints
    h.leftRemainder h.rightRemainder c
    (by simp [distinctR,Finset.card_sdiff (Finset.subset_univ _),Coord,h.hab,h.hac,h.had,h.hbc,h.hbd,h.hcd])
    h.holes_subset h.rowEndpoints_card (by omega) (h.right_count_absent hac)
    h.leftRemainder_edge_card h.rightRemainder_edge_card (h.one_delta_resource_cover hac)
  refine ⟨hH,?_⟩
  exact one_delta_resource_shape (distinctR a b c d) h.leftRemainder h.rightRemainder c d h.hcd
    (by simp [distinctR]) (by simp [distinctR]) hG hJ h.leftRemainder_edge_card h.rightRemainder_edge_card
    h.leftRemainder_support h.rightRemainder_support hC

end DistinctOuterConfig
#print axioms DistinctOuterConfig.zero_delta_impossible
#print axioms DistinctOuterConfig.one_delta_remainder_shape
end
end Snake9
