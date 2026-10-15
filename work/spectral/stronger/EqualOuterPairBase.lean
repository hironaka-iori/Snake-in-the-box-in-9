import LocalDenseRows
import StarOuterBase

namespace Snake9
open SquareIncidence Finset Classical
noncomputable section
set_option maxHeartbeats 1800000

structure EqualOuterPairConfig {m : Nat} (p : Snake m) (a b c d : Coord) where
  outer : DistinctOuterConfig p a b c d
  i : Coord
  j : Coord
  hi : i∈distinctR a b c d
  hj : j∈distinctR a b c d
  hij : i≠j
  left_eq : outer.left.F={{b,d},{i,j}}
  right_eq : outer.right.F={{a,c},{i,j}}

namespace EqualOuterPairConfig
variable {m : Nat} {p : Snake m} {a b c d : Coord} (h : EqualOuterPairConfig p a b c d)
include h

def clean : Finset Coord := distinctR a b c d\{h.i,h.j}

theorem mem_clean (k : Coord) : k∈h.clean ↔ k∈distinctR a b c d ∧ k≠h.i ∧ k≠h.j := by
  simp [clean]

theorem ordinary_corners (x y : Coord) (hx : x∈distinctR a b c d)
    (hy : y∈distinctR a b c d) (hxy : x≠y) (hne : ({x,y}:Finset Coord)≠{h.i,h.j}) :
    InPath p (pair x y) ∧ InPath p (quad a b x y) := by
  have hhx := (mem_distinctR a b c d x).mp hx
  have hhy := (mem_distinctR a b c d y).mp hy
  constructor
  · apply (h.outer.left.selected_iff x y hxy hhx.1 hhx.2.2.1 hhy.1 hhy.2.2.1).mpr
    rw [h.left_eq]
    simpa only [mem_insert,mem_singleton,not_or] using
      And.intro (delta_pair_ne x y b d hhx.2.1 hhx.2.2.2) hne
  · apply (h.outer.right_pair_iff x y hxy hhx.2.1 hhx.2.2.2 hhy.2.1 hhy.2.2.2).mpr
    rw [h.right_eq]
    simpa only [mem_insert,mem_singleton,not_or] using
      And.intro (delta_pair_ne x y a c hhx.1 hhx.2.2.1) hne

def toLocal : LocalDenseRows p a b c d where
  outer := h.outer
  rows := h.clean
  ordinary_corners := by
    intro x y hx hxR hyR hxy
    have hh := (h.mem_clean x).mp hx
    exact h.ordinary_corners x y hxR hyR hxy (delta_pair_ne x y h.i h.j hh.2.1 hh.2.2)

theorem row_selected (k : Coord) (hk : k∈distinctR a b c d) : InPath p (pair b k) := by
  have hh := (mem_distinctR a b c d k).mp hk
  have hi := (mem_distinctR a b c d h.i).mp h.hi
  have hj := (mem_distinctR a b c d h.j).mp h.hj
  apply (h.outer.left.selected_iff b k (Ne.symm hh.2.1) (Ne.symm h.outer.hab)
    h.outer.hbc hh.1 hh.2.2.1).mpr
  rw [h.left_eq]
  simpa only [mem_insert,mem_singleton,not_or] using And.intro
    (delta_pair_ne_right b k b d hh.2.1 hh.2.2.2)
    (delta_pair_ne b k h.i h.j (Ne.symm hi.2.1) (Ne.symm hj.2.1))

theorem side_pair (k : Coord) (hk : k∈distinctR a b c d) : InPath p (pair d k) := by
  have hh := (mem_distinctR a b c d k).mp hk
  have hi := (mem_distinctR a b c d h.i).mp h.hi
  have hj := (mem_distinctR a b c d h.j).mp h.hj
  apply (h.outer.left.selected_iff d k (Ne.symm hh.2.2.2) (Ne.symm h.outer.had)
    (Ne.symm h.outer.hcd) hh.1 hh.2.2.1).mpr
  rw [h.left_eq]
  simpa only [mem_insert,mem_singleton,not_or] using And.intro
    (delta_pair_ne_right d k b d hh.2.1 hh.2.2.2)
    (delta_pair_ne d k h.i h.j (Ne.symm hi.2.2.2) (Ne.symm hj.2.2.2))

theorem side_quad (k : Coord) (hk : k∈distinctR a b c d) : InPath p (quad a b c k) := by
  have hh := (mem_distinctR a b c d k).mp hk
  have hi := (mem_distinctR a b c d h.i).mp h.hi
  have hj := (mem_distinctR a b c d h.j).mp h.hj
  apply (h.outer.right_pair_iff c k (Ne.symm hh.2.2.1) (Ne.symm h.outer.hbc)
    h.outer.hcd hh.2.1 hh.2.2.2).mpr
  rw [h.right_eq]
  simpa only [mem_insert,mem_singleton,not_or] using And.intro
    (delta_pair_ne_right c k a c hh.1 hh.2.2.1)
    (delta_pair_ne c k h.i h.j (Ne.symm hi.2.2.1) (Ne.symm hj.2.2.1))

def mirror : EqualOuterPairConfig (translate p (pair a b)) b a d c where
  outer := h.outer.mirror
  i := h.i
  j := h.j
  hi := by
    have hh := (mem_distinctR a b c d h.i).mp h.hi
    exact (mem_distinctR b a d c h.i).mpr ⟨hh.2.1,hh.1,hh.2.2.2,hh.2.2.1⟩
  hj := by
    have hh := (mem_distinctR a b c d h.j).mp h.hj
    exact (mem_distinctR b a d c h.j).mpr ⟨hh.2.1,hh.1,hh.2.2.2,hh.2.2.1⟩
  hij := h.hij
  left_eq := h.right_eq
  right_eq := h.left_eq

theorem absent_pair_a (k : Coord) (hka : k≠a) (hkb : k≠b) :
    ¬InPath p (pair a k) := h.toLocal.absent_middle_pair k hka hkb

theorem absent_hole_pair : ¬InPath p (pair h.i h.j) := by
  intro hs
  have hi := (mem_distinctR a b c d h.i).mp h.hi
  have hj := (mem_distinctR a b c d h.j).mp h.hj
  apply (h.outer.left.selected_iff h.i h.j h.hij hi.1 hi.2.2.1 hj.1 hj.2.2.1).mp hs
  rw [h.left_eq]; simp

theorem absent_hole_quad : ¬InPath p (quad a b h.i h.j) := by
  intro hs
  have hi := (mem_distinctR a b c d h.i).mp h.hi
  have hj := (mem_distinctR a b c d h.j).mp h.hj
  apply (h.outer.right_pair_iff h.i h.j h.hij hi.2.1 hi.2.2.2 hj.2.1 hj.2.2.2).mp hs
  rw [h.right_eq]; simp

theorem hole_neighbor_cover : ∀w,InPath p w → Adj (triple a h.i h.j) w →
    ∃k,k≠a ∧ k≠b ∧ k≠h.i ∧ k≠h.j ∧ w=quad a h.i h.j k := by
  have hi := (mem_distinctR a b c d h.i).mp h.hi
  have hj := (mem_distinctR a b c d h.j).mp h.hj
  intro w hw hadj
  obtain ⟨k,rfl⟩ := neighbor_triple a h.i h.j hadj
  by_cases hka : k=a
  · subst k; rw [quad_cancel_first] at hw; exact False.elim (h.absent_hole_pair hw)
  by_cases hki : k=h.i
  · rw [hki,quad_cancel_second] at hw
    exact False.elim (h.absent_pair_a h.j hj.1 hj.2.1 hw)
  by_cases hkj : k=h.j
  · rw [hkj,quad_cancel_third] at hw
    exact False.elim (h.absent_pair_a h.i hi.1 hi.2.1 hw)
  by_cases hkb : k=b
  · subst k
    have he : quad a h.i h.j b=quad a b h.i h.j := by
      apply Fin.ext; dsimp [quad,triple,pair,vxor]; ac_rfl
    exact False.elim (h.absent_hole_quad (he ▸ hw))
  exact ⟨k,hka,hkb,hki,hkj,rfl⟩

theorem extension_missing (f : MissingAtNeighbor p a b) (k : Coord)
    (hk : k∈h.clean) (hq : InPath p (quad a h.i h.j k)) :
    ({h.i,k}:Finset Coord)∈f.F ∧ ({h.j,k}:Finset Coord)∈f.F := by
  obtain ⟨hkR,hki,hkj⟩ := (h.mem_clean k).mp hk
  have hh := (mem_distinctR a b c d k).mp hkR
  have hi := (mem_distinctR a b c d h.i).mp h.hi
  have hj := (mem_distinctR a b c d h.j).mp h.hj
  have hiN : ({h.i,k}:Finset Coord)≠{h.i,h.j} := delta_pair_ne_right _ _ _ _ hki hkj
  have hjN : ({h.j,k}:Finset Coord)≠{h.i,h.j} := delta_pair_ne_right _ _ _ _ hki hkj
  constructor
  · by_contra hn
    have hs := h.ordinary_corners h.i k h.hi hkR (Ne.symm hki) hiN
    have ht := (f.selected_iff h.i k (Ne.symm hki) hi.1 hi.2.1 hh.1 hh.2.1).mpr hn
    apply two_layer_saturation p a b h.i k h.j h.outer.hab hj.1 hj.2.1 hs.1 hs.2 ht
    simpa only [quad_swap_last a h.i h.j k] using hq
  · by_contra hn
    have hs := h.ordinary_corners h.j k h.hj hkR (Ne.symm hkj) hjN
    have ht := (f.selected_iff h.j k (Ne.symm hkj) hj.1 hj.2.1 hh.1 hh.2.1).mpr hn
    apply two_layer_saturation p a b h.j k h.i h.outer.hab hi.1 hi.2.1 hs.1 hs.2 ht
    have he : quad a h.i h.j k=quad a h.j k h.i := by
      apply Fin.ext; dsimp [quad,triple,pair,vxor]; ac_rfl
    exact he ▸ hq

theorem special_extension_missing (f : MissingAtNeighbor p a b) (s : Coord)
    (hsa : s≠a) (hsb : s≠b) (hsi : s≠h.i) (hsj : s≠h.j)
    (ht : InPath p (triple a h.i h.j)) (hq : InPath p (quad a h.i h.j s)) :
    ({s,h.i}:Finset Coord)∈f.F ∨ ({s,h.j}:Finset Coord)∈f.F := by
  by_contra hn
  push_neg at hn
  have hi := (mem_distinctR a b c d h.i).mp h.hi
  have hj := (mem_distinctR a b c d h.j).mp h.hj
  have hti := (f.selected_iff s h.i hsi hsa hsb hi.1 hi.2.1).mpr hn.1
  have htj := (f.selected_iff s h.j hsj hsa hsb hj.1 hj.2.1).mpr hn.2
  exact ordinary_quad_absent p a h.i h.j s (Ne.symm hi.1) (Ne.symm h.hij) hsi (Ne.symm hsj)
    ht (by simpa only [triple_swap a s h.i] using hti)
    (by simpa only [triple_swap a s h.j] using htj) hq

end EqualOuterPairConfig
#print axioms EqualOuterPairConfig.extension_missing
#print axioms EqualOuterPairConfig.special_extension_missing
end
end Snake9
