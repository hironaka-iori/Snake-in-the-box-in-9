import DenseRowGroups
import CommonHolePairs

namespace Snake9
open SquareIncidence Finset Classical
noncomputable section
set_option maxHeartbeats 1800000

structure StarOuterConfig {m : Nat} (p : Snake m) (a b c d : Coord) where
  outer : DistinctOuterConfig p a b c d
  e : Coord
  f : Coord
  he : e∈distinctR a b c d
  hf : f∈distinctR a b c d
  left_eq : outer.left.F={{b,d},{d,e}}
  right_eq : outer.right.F={{a,c},{c,f}}

namespace StarOuterConfig
variable {m : Nat} {p : Snake m} {a b c d : Coord} (h : StarOuterConfig p a b c d)
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
    · exact delta_pair_ne i j b d hib hid
    · intro he
      have hm : d∈({i,j}:Finset Coord) := he.symm ▸ (by simp : d∈({d,h.e}:Finset Coord))
      simp only [Finset.mem_insert,Finset.mem_singleton] at hm
      exact hm.elim (Ne.symm hid) (Ne.symm hjd)
  · apply (h.outer.right_pair_iff i j hij hib hid hjb hjd).mpr
    rw [h.right_eq]
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or]
    constructor
    · exact delta_pair_ne i j a c hia hic
    · intro he
      have hm : c∈({i,j}:Finset Coord) := he.symm ▸ (by simp : c∈({c,h.f}:Finset Coord))
      simp only [Finset.mem_insert,Finset.mem_singleton] at hm
      exact hm.elim (Ne.symm hic) (Ne.symm hjc)

def toDense : DenseRowConfig p a b c d := ⟨h.outer,h.ordinary_corners⟩

theorem row_selected (k : Coord) (hk : k∈distinctR a b c d) : InPath p (pair b k) := by
  obtain ⟨hka,hkb,hkc,hkd⟩ := (mem_distinctR a b c d k).mp hk
  have he := (mem_distinctR a b c d h.e).mp h.he
  apply (h.outer.left.selected_iff b k (Ne.symm hkb) (Ne.symm h.outer.hab) h.outer.hbc hka hkc).mpr
  rw [h.left_eq]
  simp only [Finset.mem_insert,Finset.mem_singleton,not_or]
  exact ⟨delta_pair_ne_right b k b d hkb hkd,delta_pair_ne b k d h.e h.outer.hbd (Ne.symm he.2.1)⟩

theorem side_pair (k : Coord) (hk : k∈distinctR a b c d) (hke : k≠h.e) : InPath p (pair d k) := by
  obtain ⟨hka,hkb,hkc,hkd⟩ := (mem_distinctR a b c d k).mp hk
  apply (h.outer.left.selected_iff d k (Ne.symm hkd) (Ne.symm h.outer.had)
    (Ne.symm h.outer.hcd) hka hkc).mpr
  rw [h.left_eq]
  simp only [Finset.mem_insert,Finset.mem_singleton,not_or]
  exact ⟨delta_pair_ne_right d k b d hkb hkd,delta_pair_ne_right d k d h.e hkd hke⟩

theorem side_quad (k : Coord) (hk : k∈distinctR a b c d) (hkf : k≠h.f) : InPath p (quad a b c k) := by
  obtain ⟨hka,hkb,hkc,hkd⟩ := (mem_distinctR a b c d k).mp hk
  apply (h.outer.right_pair_iff c k (Ne.symm hkc) (Ne.symm h.outer.hbc) h.outer.hcd hkb hkd).mpr
  rw [h.right_eq]
  simp only [Finset.mem_insert,Finset.mem_singleton,not_or]
  exact ⟨delta_pair_ne_right c k a c hka hkc,delta_pair_ne_right c k c h.f hkc hkf⟩

def mirror : StarOuterConfig (translate p (pair a b)) b a d c where
  outer := h.outer.mirror
  e := h.f
  f := h.e
  he := by
    have hh := (mem_distinctR a b c d h.f).mp h.hf
    exact (mem_distinctR b a d c h.f).mpr ⟨hh.2.1,hh.1,hh.2.2.2,hh.2.2.1⟩
  hf := by
    have hh := (mem_distinctR a b c d h.e).mp h.he
    exact (mem_distinctR b a d c h.e).mpr ⟨hh.2.1,hh.1,hh.2.2.2,hh.2.2.1⟩
  left_eq := h.right_eq
  right_eq := h.left_eq

theorem ordinary_b_absent (i j : Coord) (hi : i∈distinctR a b c d)
    (hj : j∈distinctR a b c d) (hij : i≠j) : ¬InPath p (triple b i j) := by
  have hhi := (mem_distinctR a b c d i).mp hi
  have hhj := (mem_distinctR a b c d j).mp hj
  have hs := h.ordinary_corners i j hi hj hij
  exact middle_row_triple_forbidden p a b i j h.outer.hab (Ne.symm hhi.1)
    (Ne.symm hhj.1) (Ne.symm hhi.2.1) (Ne.symm hhj.2.1) hij (h.row_selected i hi) hs.1 hs.2

theorem missing_pair_cover (f : MissingAtNeighbor p a b) (i j : Coord)
    (hi : i∈distinctR a b c d) (hj : j∈distinctR a b c d) (hij : i≠j)
    (hm : ({i,j}:Finset Coord)∈f.F) :
    ∀w,InPath p w → Adj (pair i j) w → w=triple i j c ∨ w=triple i j d := by
  have hhi := (mem_distinctR a b c d i).mp hi
  have hhj := (mem_distinctR a b c d j).mp hj
  have hs := h.ordinary_corners i j hi hj hij
  have hna : ¬InPath p (triple a i j) := fun ht =>
    (f.selected_iff i j hij hhi.1 hhi.2.1 hhj.1 hhj.2.1).mp ht hm
  intro w hw hadj
  obtain ⟨r,rfl⟩ := neighbor_pair i j hadj
  by_cases hri : r=i
  · subst r; rw [triple_cancel_left] at hw
    exact False.elim (h.outer.absent_unit j hhj.1 hhj.2.2.1 hw)
  by_cases hrj : r=j
  · subst r; rw [triple_cancel_right] at hw
    exact False.elim (h.outer.absent_unit i hhi.1 hhi.2.2.1 hw)
  by_cases hra : r=a
  · subst r; rw [triple_rotate] at hw; exact False.elim (hna hw)
  by_cases hrb : r=b
  · subst r; rw [triple_rotate] at hw; exact False.elim (h.ordinary_b_absent i j hi hj hij hw)
  by_cases hrc : r=c
  · subst r; exact Or.inl rfl
  by_cases hrd : r=d
  · subst r; exact Or.inr rfl
  have hr := (mem_distinctR a b c d r).mpr ⟨hra,hrb,hrc,hrd⟩
  exact False.elim (selected_triple_forbidden p i j r hij (Ne.symm hri) (Ne.symm hrj)
    hs.1 (h.ordinary_corners i r hi hr (Ne.symm hri)).1
    (h.ordinary_corners j r hj hr (Ne.symm hrj)).1 hw)

theorem missing_pair_low (f : MissingAtNeighbor p a b) (i j : Coord)
    (hi : i∈distinctR a b c d) (hj : j∈distinctR a b c d) (hij : i≠j)
    (hie : i≠h.e) (hje : j≠h.e) (hm : ({i,j}:Finset Coord)∈f.F) :
    AtMostOneNeighbor p (pair i j) := by
  have hhi := (mem_distinctR a b c d i).mp hi
  have hhj := (mem_distinctR a b c d j).mp hj
  have unique (w : Vertex) (hw : InPath p w) (hadj : Adj (pair i j) w) : w=triple i j c := by
    rcases h.missing_pair_cover f i j hi hj hij hm w hw hadj with he | he
    · exact he
    · have hdi : InPath p (pair i d) := by simpa only [pair_comm d i] using h.side_pair i hi hie
      have hdj : InPath p (pair j d) := by simpa only [pair_comm d j] using h.side_pair j hj hje
      exact False.elim (selected_triple_forbidden p i j d hij hhi.2.2.2 hhj.2.2.2
        (h.ordinary_corners i j hi hj hij).1 hdi hdj (he ▸ hw))
  intro x y hx hy hax hay
  exact (unique x hx hax).trans (unique y hy hay).symm

theorem missing_quad_low (f : MissingAtNeighbor p a b) (i j : Coord)
    (hi : i∈distinctR a b c d) (hj : j∈distinctR a b c d) (hij : i≠j)
    (hif : i≠h.f) (hjf : j≠h.f) (hm : ({i,j}:Finset Coord)∈f.F) :
    AtMostOneNeighbor p (quad a b i j) := by
  have hi' : i∈distinctR b a d c := by
    have hh := (mem_distinctR a b c d i).mp hi
    exact (mem_distinctR b a d c i).mpr ⟨hh.2.1,hh.1,hh.2.2.2,hh.2.2.1⟩
  have hj' : j∈distinctR b a d c := by
    have hh := (mem_distinctR a b c d j).mp hj
    exact (mem_distinctR b a d c j).mpr ⟨hh.2.1,hh.1,hh.2.2.2,hh.2.2.1⟩
  have hl := h.mirror.missing_pair_low f.mirror i j hi' hj' hij hif hjf hm
  have ht := low_of_translate p (pair a b) (pair i j) hl
  simpa only [quad,triple,pair,vxor_assoc] using ht

end StarOuterConfig
#print axioms StarOuterConfig.missing_quad_low
end
end Snake9
