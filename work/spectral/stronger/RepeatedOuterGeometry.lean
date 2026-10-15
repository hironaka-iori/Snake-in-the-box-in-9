import RepeatedOuterConfig

namespace Snake9
open Finset Classical
noncomputable section
set_option maxHeartbeats 1500000

theorem neighbor_other_of_not_low {m : Nat} (p : Snake m) (v z : Vertex)
    (h : ¬AtMostOneNeighbor p v) :
    ∃w,InPath p w ∧ Adj v w ∧ w≠z := by
  by_contra hn
  have he : ∀w,InPath p w→Adj v w→w=z := by
    intro w hw ha
    by_contra hwz
    exact hn ⟨w,hw,ha,hwz⟩
  exact h (fun u w hu hw hau haw => (he u hu hau).trans (he w hw haw).symm)

namespace RepeatedOuterConfig
variable {m : Nat} {p : Snake m} {a b c : Coord} (h : RepeatedOuterConfig p a b c)
include h

theorem row_neighbor_cover (k : Coord) (hk : k∈repeatedR a b c)
    (w : Vertex) (hw : InPath p w) (hadj : Adj (pair b k) w) :
    w=triple b k c ∨ ∃l,l∈repeatedR a b c ∧ l≠k ∧ w=triple b k l := by
  obtain ⟨hka,hkb,hkc⟩ := (mem_repeatedR a b c k).mp hk
  obtain ⟨l,rfl⟩ := neighbor_pair b k hadj
  by_cases hlb : l=b
  · subst l
    rw [triple_cancel_left] at hw
    exact False.elim (h.absent_unit k hka hkc hw)
  by_cases hlk : l=k
  · subst l
    rw [triple_cancel_right] at hw
    exact False.elim (h.absent_unit b (Ne.symm h.hab) h.hbc hw)
  by_cases hla : l=a
  · subst l
    rw [triple_rotate] at hw
    exact False.elim (h.absent_abk k hkb hkc hw)
  by_cases hlc : l=c
  · subst l
    exact Or.inl rfl
  exact Or.inr ⟨l,(mem_repeatedR a b c l).mpr ⟨hla,hlb,hlc⟩,hlk,rfl⟩

theorem row_connection_missing (k l : Coord) (hk : k∈repeatedR a b c)
    (hl : l∈repeatedR a b c) (hkl : k≠l)
    (hbk : InPath p (pair b k)) (hconn : InPath p (triple b k l)) :
    (({k,l}:Finset Coord)∈h.left.F ∨ ({k,l}:Finset Coord)∈h.right.F) ∧
    (InPath p (pair b l) → ({k,l}:Finset Coord)∈h.left.F ∧ ({k,l}:Finset Coord)∈h.right.F) := by
  obtain ⟨hka,hkb,hkc⟩ := (mem_repeatedR a b c k).mp hk
  obtain ⟨hla,hlb,hlc⟩ := (mem_repeatedR a b c l).mp hl
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
    have hs2 := (h.right_pair_iff k l hkl hkb hkc hlb hlc).mpr hn2
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
      have hs2 := (h.right_pair_iff k l hkl hkb hkc hlb hlc).mpr hn
      have adjl : Adj (triple b k l) (pair b l) := by
        rw [triple_swap]
        exact adj_symmetric (pair_triple_adj _ _ _)
      rcases selected_three_neighbors_repeat p hconn hbk hbl hs2 adj0 adjl adj2 with he | he | he
      · exact hkl (pair_injective_right b k l he)
      · exact neq02 he
      · have hb := congrArg (fun v : Vertex => v.val.testBit a.val) he
        simp [bit_pair,bit_quad,Ne.symm h.hab,hka,hla] at hb

end RepeatedOuterConfig

#print axioms RepeatedOuterConfig.row_connection_missing
end
end Snake9
