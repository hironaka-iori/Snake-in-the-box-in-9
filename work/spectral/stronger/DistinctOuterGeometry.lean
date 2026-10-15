import DistinctOuterConfig

namespace Snake9
open Finset Classical
noncomputable section
set_option maxHeartbeats 1500000
namespace DistinctOuterConfig
variable {m : Nat} {p : Snake m} {a b c d : Coord} (h : DistinctOuterConfig p a b c d)
include h
theorem row_connection_missing (k l : Coord) (hk : k∈distinctR a b c d)
    (hl : l∈distinctR a b c d) (hkl : k≠l)
    (hbk : InPath p (pair b k)) (hconn : InPath p (triple b k l)) :
    (({k,l}:Finset Coord)∈h.left.F ∨ ({k,l}:Finset Coord)∈h.right.F) ∧
    (InPath p (pair b l) → ({k,l}:Finset Coord)∈h.left.F ∧ ({k,l}:Finset Coord)∈h.right.F) := by
  obtain ⟨hka,hkb,hkc,hkd⟩ := (mem_distinctR a b c d k).mp hk
  obtain ⟨hla,hlb,hlc,hld⟩ := (mem_distinctR a b c d l).mp hl
  have hqeq : quad a b k l=quad b k l a := by
    apply Fin.ext
    dsimp [quad,triple,pair,vxor]
    ac_rfl
  have adj0 : Adj (triple b k l) (pair b k) := adj_symmetric (pair_triple_adj _ _ _)
  have adj1 : Adj (triple b k l) (pair k l) := by
    rw [←triple_rotate k l b]
    exact adj_symmetric (pair_triple_adj _ _ _)
  have adj2 : Adj (triple b k l) (quad a b k l) := by
    rw [hqeq]
    exact triple_quad_adj _ _ _ _
  have neq01 : pair b k≠pair k l := by
    intro he
    have hb := congrArg (fun v : Vertex => v.val.testBit b.val) he
    simp [bit_pair,hkb,hlb] at hb
  have neq02 : pair b k≠quad a b k l := by
    intro he
    have hb := congrArg (fun v : Vertex => v.val.testBit a.val) he
    simp [bit_pair,bit_quad,Ne.symm h.hab,hka,hla] at hb
  have neq12 : pair k l≠quad a b k l := by
    intro he
    have hb := congrArg (fun v : Vertex => v.val.testBit a.val) he
    simp [bit_pair,bit_quad,Ne.symm h.hab,hka,hla] at hb
  constructor
  · by_contra hn
    have hn0 : ({k,l}:Finset Coord)∉h.left.F := fun he => hn (Or.inl he)
    have hn2 : ({k,l}:Finset Coord)∉h.right.F := fun he => hn (Or.inr he)
    have hs0 := (h.left.selected_iff k l hkl hka hkc hla hlc).mpr hn0
    have hs2 := (h.right_pair_iff k l hkl hkb hkd hlb hld).mpr hn2
    rcases selected_three_neighbors_repeat p hconn hbk hs0 hs2 adj0 adj1 adj2 with he | he | he
    · exact neq01 he
    · exact neq02 he
    · exact neq12 he
  · intro hbl
    constructor
    · by_contra hn
      have hs0 := (h.left.selected_iff k l hkl hka hkc hla hlc).mpr hn
      exact selected_triple_forbidden p b k l (Ne.symm hkb) (Ne.symm hlb) hkl hbk hbl hs0 hconn
    · by_contra hn
      have hs2 := (h.right_pair_iff k l hkl hkb hkd hlb hld).mpr hn
      have adjl : Adj (triple b k l) (pair b l) := by
        rw [triple_swap]
        exact adj_symmetric (pair_triple_adj _ _ _)
      rcases selected_three_neighbors_repeat p hconn hbk hbl hs2 adj0 adjl adj2 with he | he | he
      · exact hkl (pair_injective_right b k l he)
      · exact neq02 he
      · have hb := congrArg (fun v : Vertex => v.val.testBit a.val) he
        simp [bit_pair,bit_quad,Ne.symm h.hab,hka,hla] at hb

theorem c_connection_missing (k : Coord) (hk : k∈distinctR a b c d)
    (hbk : InPath p (pair b k)) (hconn : InPath p (triple b k c)) :
    ({a,c}:Finset Coord)∈h.right.F ∨ ({c,k}:Finset Coord)∈h.right.F := by
  obtain ⟨hka,hkb,hkc,hkd⟩ := (mem_distinctR a b c d k).mp hk
  by_contra hn
  have hn0 : ({a,c}:Finset Coord)∉h.right.F := fun he => hn (Or.inl he)
  have hn1 : ({c,k}:Finset Coord)∉h.right.F := fun he => hn (Or.inr he)
  have hbc : InPath p (pair b c) := by
    have hh := (h.right_pair_iff a c h.hac h.hab h.had (Ne.symm h.hbc) h.hcd).mpr hn0
    rwa [quad_swap_last,quad_cancel_first] at hh
  have hq : InPath p (quad a b k c) := by
    rw [quad_swap_last]
    exact (h.right_pair_iff c k (Ne.symm hkc) (Ne.symm h.hbc) h.hcd hkb hkd).mpr hn1
  have heq : quad a b k c=quad b k c a := by
    apply Fin.ext; dsimp [quad,triple,pair,vxor]; ac_rfl
  have ha0 : Adj (triple b k c) (pair b k) := adj_symmetric (pair_triple_adj _ _ _)
  have ha1 : Adj (triple b k c) (pair b c) := by
    rw [triple_swap]
    exact adj_symmetric (pair_triple_adj _ _ _)
  have ha2 : Adj (triple b k c) (quad a b k c) := by rw [heq]; exact triple_quad_adj _ _ _ _
  rcases selected_three_neighbors_repeat p hconn hbk hbc hq ha0 ha1 ha2 with he | he | he
  · exact hkc (pair_injective_right b k c he)
  · have hb := congrArg (fun v : Vertex => v.val.testBit a.val) he
    simp [bit_pair,bit_quad,Ne.symm h.hab,Ne.symm h.hac,hka] at hb
  · have hb := congrArg (fun v : Vertex => v.val.testBit a.val) he
    simp [bit_pair,bit_quad,Ne.symm h.hab,Ne.symm h.hac,hka] at hb

theorem d_connection_missing (k : Coord) (hk : k∈distinctR a b c d)
    (hbk : InPath p (pair b k)) (hconn : InPath p (triple b k d)) :
    ({b,d}:Finset Coord)∈h.left.F ∨ ({d,k}:Finset Coord)∈h.left.F := by
  obtain ⟨hka,hkb,hkc,hkd⟩ := (mem_distinctR a b c d k).mp hk
  by_contra hn
  have hn0 : ({b,d}:Finset Coord)∉h.left.F := fun he => hn (Or.inl he)
  have hn1 : ({d,k}:Finset Coord)∉h.left.F := fun he => hn (Or.inr he)
  have hbd := (h.left.selected_iff b d h.hbd (Ne.symm h.hab) h.hbc (Ne.symm h.had) (Ne.symm h.hcd)).mpr hn0
  have hdk := (h.left.selected_iff d k (Ne.symm hkd) (Ne.symm h.had) (Ne.symm h.hcd) hka hkc).mpr hn1
  rw [pair_comm] at hdk
  exact selected_triple_forbidden p b k d (Ne.symm hkb) h.hbd hkd hbk hbd hdk hconn

end DistinctOuterConfig
#print axioms DistinctOuterConfig.row_connection_missing
#print axioms DistinctOuterConfig.c_connection_missing
#print axioms DistinctOuterConfig.d_connection_missing
end
end Snake9
