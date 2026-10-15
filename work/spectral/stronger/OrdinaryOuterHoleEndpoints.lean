import OrdinaryOuterBase

namespace Snake9
open SquareIncidence Finset Classical
noncomputable section
set_option maxHeartbeats 1800000

namespace OrdinaryOuterConfig
variable {m : Nat} {p : Snake m} {a b c d : Coord} (h : OrdinaryOuterConfig p a b c d)
include h

theorem left_hole_extension (f : MissingAtNeighbor p a b) (i j k : Coord)
    (hij : i≠j) (hA : ({i,j}:Finset Coord)=h.A)
    (hk : k∈distinctR a b c d) (hki : k≠i) (hkj : k≠j)
    (hq : InPath p (quad a i j k)) :
    (({i,k}:Finset Coord)∈f.F ∨ ({i,k}:Finset Coord)=h.B) ∧
    (({j,k}:Finset Coord)∈f.F ∨ ({j,k}:Finset Coord)=h.B) := by
  have hiR := h.Asub (hA ▸ (by simp : i∈({i,j}:Finset Coord)))
  have hjR := h.Asub (hA ▸ (by simp : j∈({i,j}:Finset Coord)))
  have hi := (mem_distinctR a b c d i).mp hiR
  have hj := (mem_distinctR a b c d j).mp hjR
  have hh := (mem_distinctR a b c d k).mp hk
  have hikA : ({i,k}:Finset Coord)≠h.A := fun he =>
    delta_pair_ne_right i k i j hki hkj (he.trans hA.symm)
  have hjkA : ({j,k}:Finset Coord)≠h.A := fun he =>
    delta_pair_ne_right j k i j hki hkj (he.trans hA.symm)
  constructor
  · by_contra hn
    push_neg at hn
    have hs := (h.left_pair_iff i k hiR hk (Ne.symm hki)).mpr hikA
    have ht := (h.right_pair_iff i k hiR hk (Ne.symm hki)).mpr hn.2
    have hm := (f.selected_iff i k (Ne.symm hki) hi.1 hi.2.1 hh.1 hh.2.1).mpr hn.1
    apply two_layer_saturation p a b i k j h.outer.hab hj.1 hj.2.1 hs ht hm
    simpa only [quad_swap_last a i j k] using hq
  · by_contra hn
    push_neg at hn
    have hs := (h.left_pair_iff j k hjR hk (Ne.symm hkj)).mpr hjkA
    have ht := (h.right_pair_iff j k hjR hk (Ne.symm hkj)).mpr hn.2
    have hm := (f.selected_iff j k (Ne.symm hkj) hj.1 hj.2.1 hh.1 hh.2.1).mpr hn.1
    apply two_layer_saturation p a b j k i h.outer.hab hi.1 hi.2.1 hs ht hm
    have he : quad a i j k=quad a j k i := by apply Fin.ext; dsimp [quad,triple,pair,vxor]; ac_rfl
    exact he ▸ hq

theorem left_hole_endpoint (f : MissingAtNeighbor p a b) (i j : Coord)
    (hij : i≠j) (hA : ({i,j}:Finset Coord)=h.A)
    (hgood : OrdinaryHoleGood f.F (distinctR a b c d) c d h.A h.B) :
    InPath p (triple a i j) ∧ AtMostOneNeighbor p (triple a i j) := by
  have hiA : i∈h.A := hA ▸ (by simp : i∈({i,j}:Finset Coord))
  have hjA : j∈h.A := hA ▸ (by simp : j∈({i,j}:Finset Coord))
  have hiR := h.Asub hiA
  have hjR := h.Asub hjA
  have hi := (mem_distinctR a b c d i).mp hiR
  have hj := (mem_distinctR a b c d j).mp hjR
  have ht := (f.selected_iff i j hij hi.1 hi.2.1 hj.1 hj.2.1).mpr (by simpa only [hA] using hgood.1)
  have special_absent (s : Coord) (hsa : s≠a) (hsb : s≠b) (hsi : s≠i) (hsj : s≠j)
      (hsiF : ({s,i}:Finset Coord)∉f.F) (hsjF : ({s,j}:Finset Coord)∉f.F) :
      ¬InPath p (quad a i j s) := by
    have hti := (f.selected_iff s i hsi hsa hsb hi.1 hi.2.1).mpr hsiF
    have htj := (f.selected_iff s j hsj hsa hsb hj.1 hj.2.1).mpr hsjF
    exact ordinary_quad_absent p a i j s (Ne.symm hi.1) (Ne.symm hij) hsi (Ne.symm hsj)
      ht (by simpa only [triple_swap a s i] using hti) (by simpa only [triple_swap a s j] using htj)
  have unique (w : Vertex) (hw : InPath p w) (hadj : Adj (triple a i j) w) : w=quad a b i j := by
    obtain ⟨k,rfl⟩ := neighbor_triple a i j hadj
    by_cases hka : k=a
    · subst k; rw [quad_cancel_first] at hw
      exact False.elim ((h.left_pair_iff i j hiR hjR hij).mp hw hA)
    by_cases hki : k=i
    · subst k; rw [quad_cancel_second] at hw
      exact False.elim (h.absent_pair_a j hj.1 hj.2.1 hw)
    by_cases hkj : k=j
    · subst k; rw [quad_cancel_third] at hw
      exact False.elim (h.absent_pair_a i hi.1 hi.2.1 hw)
    by_cases hkb : k=b
    · subst k; apply Fin.ext; dsimp [quad,triple,pair,vxor]; ac_rfl
    by_cases hkc : k=c
    · subst k
      exact False.elim (special_absent c (Ne.symm h.outer.hac) (Ne.symm h.outer.hbc)
        (Ne.symm hi.2.2.1) (Ne.symm hj.2.2.1) (hgood.2.1 i hiA).1 (hgood.2.1 j hjA).1 hw)
    by_cases hkd : k=d
    · subst k
      exact False.elim (special_absent d (Ne.symm h.outer.had) (Ne.symm h.outer.hbd)
        (Ne.symm hi.2.2.2) (Ne.symm hj.2.2.2) (hgood.2.1 i hiA).2 (hgood.2.1 j hjA).2 hw)
    have hk := (mem_distinctR a b c d k).mpr ⟨hka,hkb,hkc,hkd⟩
    have hknA : k∉h.A := by simpa only [←hA,mem_insert,mem_singleton,not_or] using And.intro hki hkj
    have hm := h.left_hole_extension f i j k hij hA hk hki hkj hw
    apply False.elim (hgood.2.2 k hk hknA _)
    intro s hs
    rw [←hA] at hs
    rcases Finset.mem_insert.mp hs with rfl | hs
    · exact hm.1
    · exact Finset.mem_singleton.mp hs ▸ hm.2
  exact ⟨ht,fun x y hx hy hax hay => (unique x hx hax).trans (unique y hy hay).symm⟩

theorem right_hole_endpoint (f : MissingAtNeighbor p a b) (i j : Coord)
    (hij : i≠j) (hB : ({i,j}:Finset Coord)=h.B)
    (hgood : OrdinaryHoleGood f.F (distinctR a b c d) c d h.B h.A) :
    InPath p (triple a i j) ∧ AtMostOneNeighbor p (triple a i j) := by
  have hgm : OrdinaryHoleGood f.mirror.F (distinctR b a d c) d c h.mirror.A h.mirror.B := by
    refine ⟨hgood.1,?_,?_⟩
    · intro s hs
      exact ⟨(hgood.2.1 s hs).2,(hgood.2.1 s hs).1⟩
    · intro r hr hrn
      have hh := (mem_distinctR b a d c r).mp hr
      exact hgood.2.2 r ((mem_distinctR a b c d r).mpr ⟨hh.2.1,hh.1,hh.2.2.2,hh.2.2.1⟩) hrn
  have hm := h.mirror.left_hole_endpoint f.mirror i j hij hB hgm
  have hsel := (inPath_translate_at p (pair a b) (triple b i j)).mp hm.1
  have hlow := low_of_translate p (pair a b) (triple b i j) hm.2
  constructor
  · simpa only [triple,pair,vxor_assoc,vxor_cancel] using hsel
  · simpa only [triple,pair,vxor_assoc,vxor_cancel] using hlow

end OrdinaryOuterConfig
#print axioms OrdinaryOuterConfig.left_hole_endpoint
#print axioms OrdinaryOuterConfig.right_hole_endpoint
end
end Snake9
