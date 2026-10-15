import DistinctOuterConfig
import SingleDeltaBase
import CubeFlipSaturation

namespace Snake9
open SquareIncidence Finset Classical
noncomputable section
set_option maxHeartbeats 1500000

theorem middle_row_triple_forbidden {m : Nat} (p : Snake m) (a b i j : Coord)
    (hab : a≠b) (hai : a≠i) (haj : a≠j) (hbi : b≠i) (hbj : b≠j) (hij : i≠j)
    (hbi_sel : InPath p (pair b i)) (hij_sel : InPath p (pair i j))
    (hq : InPath p (quad a b i j)) : ¬InPath p (triple b i j) := by
  intro ht
  have he : triple b i j=triple i j b := by
    apply Fin.ext; dsimp [triple,pair,vxor]; ac_rfl
  have heq : quad a b i j=quad b i j a := by
    apply Fin.ext; dsimp [quad,triple,pair,vxor]; ac_rfl
  rcases selected_three_neighbors_repeat p ht hbi_sel hij_sel hq
    (adj_symmetric (pair_triple_adj b i j))
    (by rw [he]; exact adj_symmetric (pair_triple_adj i j b))
    (by rw [heq]; exact triple_quad_adj b i j a) with hh | hh | hh
  · have hb := congrArg (fun v : Vertex => v.val.testBit b.val) hh
    simp [bit_pair,Ne.symm hbi,Ne.symm hbj] at hb
  · have hb := congrArg (fun v : Vertex => v.val.testBit a.val) hh
    simp [bit_pair,bit_quad,Ne.symm hab,Ne.symm hai,Ne.symm haj] at hb
  · have hb := congrArg (fun v : Vertex => v.val.testBit a.val) hh
    simp [bit_pair,bit_quad,Ne.symm hab,Ne.symm hai,Ne.symm haj] at hb

structure CommonHoleConfig {m : Nat} (p : Snake m) (a b c d : Coord) where
  outer : DistinctOuterConfig p a b c d
  e : Coord
  he : e≠a ∧ e≠b ∧ e≠c ∧ e≠d
  left_eq : outer.left.F={{b,d},{b,e}}
  right_eq : outer.right.F={{a,c},{a,e}}

namespace CommonHoleConfig
variable {m : Nat} {p : Snake m} {a b c d : Coord} (h : CommonHoleConfig p a b c d)
include h

theorem ordinary_corners (i j : Coord) (hi : i∈distinctR a b c d)
    (hj : j∈distinctR a b c d) (hij : i≠j) :
    InPath p (pair i j) ∧ InPath p (quad a b i j) := by
  obtain ⟨hia,hib,hic,hid⟩ := (mem_distinctR a b c d i).mp hi
  obtain ⟨hja,hjb,hjc,hjd⟩ := (mem_distinctR a b c d j).mp hj
  constructor
  · apply (h.outer.left.selected_iff i j hij hia hic hja hjc).mpr
    rw [h.left_eq]
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or]
    constructor
    · intro he
      have hm : b∈({i,j}:Finset Coord) := he.symm ▸ (by simp : b∈({b,d}:Finset Coord))
      simp only [Finset.mem_insert,Finset.mem_singleton] at hm
      exact hm.elim (Ne.symm hib) (Ne.symm hjb)
    · intro he
      have hm : b∈({i,j}:Finset Coord) := he.symm ▸ (by simp : b∈({b,h.e}:Finset Coord))
      simp only [Finset.mem_insert,Finset.mem_singleton] at hm
      exact hm.elim (Ne.symm hib) (Ne.symm hjb)
  · apply (h.outer.right_pair_iff i j hij hib hid hjb hjd).mpr
    rw [h.right_eq]
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or]
    constructor
    · intro he
      have hm : a∈({i,j}:Finset Coord) := he.symm ▸ (by simp : a∈({a,c}:Finset Coord))
      simp only [Finset.mem_insert,Finset.mem_singleton] at hm
      exact hm.elim (Ne.symm hia) (Ne.symm hja)
    · intro he
      have hm : a∈({i,j}:Finset Coord) := he.symm ▸ (by simp : a∈({a,h.e}:Finset Coord))
      simp only [Finset.mem_insert,Finset.mem_singleton] at hm
      exact hm.elim (Ne.symm hia) (Ne.symm hja)

theorem active_corners (k : Coord) (hk : k∈distinctR a b c d) (hke : k≠h.e) :
    InPath p (pair b k) ∧ InPath p (pair d k) ∧ InPath p (quad a b c k) := by
  obtain ⟨hka,hkb,hkc,hkd⟩ := (mem_distinctR a b c d k).mp hk
  constructor
  · apply (h.outer.left.selected_iff b k (Ne.symm hkb) (Ne.symm h.outer.hab)
      h.outer.hbc hka hkc).mpr
    rw [h.left_eq]
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or]
    exact ⟨delta_pair_ne_right b k b d hkb hkd,delta_pair_ne_right b k b h.e hkb hke⟩
  constructor
  · apply (h.outer.left.selected_iff d k (Ne.symm hkd) (Ne.symm h.outer.had)
      (Ne.symm h.outer.hcd) hka hkc).mpr
    rw [h.left_eq]
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or]
    constructor
    · intro he
      have hm : b∈({d,k}:Finset Coord) := he.symm ▸ (by simp : b∈({b,d}:Finset Coord))
      simp only [Finset.mem_insert,Finset.mem_singleton] at hm
      exact hm.elim h.outer.hbd (Ne.symm hkb)
    · exact delta_pair_ne d k b h.e (Ne.symm h.outer.hbd) (Ne.symm h.he.2.2.2)
  · apply (h.outer.right_pair_iff c k (Ne.symm hkc) (Ne.symm h.outer.hbc)
      h.outer.hcd hkb hkd).mpr
    rw [h.right_eq]
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or]
    exact ⟨delta_pair_ne_right c k a c hka hkc,
      delta_pair_ne c k a h.e (Ne.symm h.outer.hac) (Ne.symm h.he.2.2.1)⟩

theorem row_cover (k : Coord) (hk : k∈distinctR a b c d) (hke : k≠h.e)
    (w : Vertex) (hw : InPath p w) (hadj : Adj (pair b k) w) :
    w=triple b k c ∨ w=triple b k d := by
  rcases h.outer.row_neighbor_cover k hk w hw hadj with he | he | ⟨l,hl,hlk,he⟩
  · exact Or.inl he
  · exact Or.inr he
  · have hh := (mem_distinctR a b c d k).mp hk
    have hh' := (mem_distinctR a b c d l).mp hl
    have hs := h.ordinary_corners k l hk hl (Ne.symm hlk)
    exact False.elim (middle_row_triple_forbidden p a b k l h.outer.hab
      (Ne.symm hh.1) (Ne.symm hh'.1) (Ne.symm hh.2.1) (Ne.symm hh'.2.1)
      (Ne.symm hlk) (h.active_corners k hk hke).1 hs.1 hs.2 (he ▸ hw))

theorem active_middle_selected (f : MissingAtNeighbor p a b) (k : Coord)
    (hk : k∈distinctR a b c d) (hisol : ∀s∈f.F,k∉s) :
    InPath p (triple a c k) ∧ InPath p (triple a d k) := by
  obtain ⟨hka,hkb,hkc,hkd⟩ := (mem_distinctR a b c d k).mp hk
  constructor
  · apply (f.selected_iff c k (Ne.symm hkc) (Ne.symm h.outer.hac)
      (Ne.symm h.outer.hbc) hka hkb).mpr
    intro hm; exact hisol _ hm (by simp)
  · apply (f.selected_iff d k (Ne.symm hkd) (Ne.symm h.outer.had)
      (Ne.symm h.outer.hbd) hka hkb).mpr
    intro hm; exact hisol _ hm (by simp)

end CommonHoleConfig
#print axioms CommonHoleConfig.row_cover
end
end Snake9
