import GeneralOneTwoLocal

namespace Snake9
open Finset Classical
noncomputable section
set_option maxHeartbeats 1500000
set_option maxRecDepth 100000

structure MiddleMatchingConfig {m : Nat} (p : Snake m) (a b c : Coord) where
  hab : a≠b
  hac : a≠c
  hbc : b≠c
  h0 : InPath p 0
  ha : InPath p (unit a)
  hc : InPath p (unit c)
  hab_selected : InPath p (pair a b)
  habc_selected : InPath p (triple a b c)
  G : Finset (Finset Coord)
  Gcard : G.card=2
  edge_card : ∀s∈G,s.card=2
  avoids : ∀s∈G,∀k∈s,k≠a ∧ k≠b ∧ k≠c
  matching : ∀i j,({i,j}:Finset Coord)∈G → ∀k,k≠i → k≠j →
    ({i,k}:Finset Coord)∉G ∧ ({j,k}:Finset Coord)∉G
  left_iff : ∀i j,i≠j → i≠a → i≠b → i≠c → j≠a → j≠b → j≠c →
    (InPath p (pair i j) ↔ ({i,j}:Finset Coord)∉G)
  right_iff : ∀i j,i≠j → i≠a → i≠b → i≠c → j≠a → j≠b → j≠c →
    (InPath p (quad a b i j) ↔ ({i,j}:Finset Coord)∉G)
  u : Coord
  v : Coord
  huv : u≠v
  hu : u≠a ∧ u≠b ∧ u≠c
  hv : v≠a ∧ v≠b ∧ v≠c
  isolated_u : ∀s∈G,u∉s
  isolated_v : ∀s∈G,v∉s
  hbu : InPath p (pair b u)
  hbv : InPath p (pair b v)
  low_bu : AtMostOneNeighbor p (pair b u)
  low_bv : AtMostOneNeighbor p (pair b v)

namespace MiddleMatchingConfig
variable {m : Nat} {p : Snake m} {a b c : Coord} (h : MiddleMatchingConfig p a b c)
include h

theorem absent_pair_a (k : Coord) (hka : k≠a) (hkb : k≠b) :
    ¬InPath p (pair a k) := by
  intro hk
  have hza : InPath (translate p (unit a)) (unit a) :=
    (translate_unit_membership p a a).mpr (by simpa only [pair_self] using h.h0)
  have hzb := (translate_unit_membership p a b).mpr h.hab_selected
  have hz0 : InPath (translate p (unit a)) 0 :=
    (inPath_translate_at p (unit a) 0).mpr (by simpa using h.ha)
  rcases unit_cover_two (translate p (unit a)) a b hz0 hza hzb h.hab k
    ((translate_unit_membership p a k).mpr hk) with he | he
  · exact hka he
  · exact hkb he

theorem triple_not_low (i j : Coord) (hia : i≠a) (hja : j≠a)
    (ht : InPath p (triple a i j)) : ¬AtMostOneNeighbor p (triple a i j) := by
  intro hl
  have htu : triple a i j≠pair b h.u := by
    intro he
    have hb := congrArg (fun z : Vertex => z.val.testBit a.val) he
    simp [bit_triple,bit_pair,hia,hja,Ne.symm h.hab,h.hu.1] at hb
  have htv : triple a i j≠pair b h.v := by
    intro he
    have hb := congrArg (fun z : Vertex => z.val.testBit a.val) he
    simp [bit_triple,bit_pair,hia,hja,Ne.symm h.hab,h.hv.1] at hb
  rcases three_low_degree_vertices_repeat p h.hbu h.hbv ht h.low_bu h.low_bv hl with he | he | he
  · exact h.huv (pair_injective_right b h.u h.v he)
  · exact htu he.symm
  · exact htv he.symm

/-- A selected middle triple has its two outer corners as neighbors. -/
theorem outer_saturation (i k j : Coord)
    (hia : i≠a) (hib : i≠b) (hka : k≠a) (hkb : k≠b)
    (hja : j≠a) (hjb : j≠b) (hji : j≠i) (hjk : j≠k)
    (hp : InPath p (pair i k)) (hq : InPath p (quad a b i k))
    (ht : InPath p (triple a i k)) : ¬InPath p (quad a i k j) := by
  intro hr
  have heq : quad a b i k=quad a i k b := by
    apply Fin.ext; dsimp [quad,triple,pair,vxor]; ac_rfl
  rcases selected_three_neighbors_repeat p ht hp hq hr
    (by have he : triple a i k=triple i k a := by
          apply Fin.ext; dsimp [triple,pair,vxor]; ac_rfl
        rw [he]; exact adj_symmetric (pair_triple_adj i k a))
    (by rw [heq]; exact triple_quad_adj a i k b)
    (triple_quad_adj a i k j) with he | he | he
  · have hb := congrArg (fun z : Vertex => z.val.testBit a.val) he
    simp [bit_pair,bit_quad,Ne.symm h.hab,hia,hka] at hb
  · have hb := congrArg (fun z : Vertex => z.val.testBit a.val) he
    simp [bit_pair,bit_quad,hia,hka,hja] at hb
  · have hb := congrArg (fun z : Vertex => z.val.testBit b.val) he
    simp [bit_quad,h.hab,hib,hkb,hjb] at hb

theorem extension_missing (f : MissingAtNeighbor p a b) (i j k : Coord)
    (hij : i≠j) (hG : ({i,j}:Finset Coord)∈h.G)
    (hka : k≠a) (hkb : k≠b) (hkc : k≠c) (hki : k≠i) (hkj : k≠j)
    (hq : InPath p (quad a i j k)) :
    ({i,k}:Finset Coord)∈f.F ∧ ({j,k}:Finset Coord)∈f.F := by
  have hi := h.avoids _ hG i (by simp)
  have hj := h.avoids _ hG j (by simp)
  have hg := h.matching i j hG k hki hkj
  constructor
  · by_contra hn
    have ht := (f.selected_iff i k (Ne.symm hki) hi.1 hi.2.1 hka hkb).mpr hn
    have hp := (h.left_iff i k (Ne.symm hki) hi.1 hi.2.1 hi.2.2 hka hkb hkc).mpr hg.1
    have hq' := (h.right_iff i k (Ne.symm hki) hi.1 hi.2.1 hi.2.2 hka hkb hkc).mpr hg.1
    apply h.outer_saturation i k j hi.1 hi.2.1 hka hkb hj.1 hj.2.1 (Ne.symm hij) (Ne.symm hkj) hp hq' ht
    simpa only [quad_swap_last a i j k] using hq
  · by_contra hn
    have ht := (f.selected_iff j k (Ne.symm hkj) hj.1 hj.2.1 hka hkb).mpr hn
    have hp := (h.left_iff j k (Ne.symm hkj) hj.1 hj.2.1 hj.2.2 hka hkb hkc).mpr hg.2
    have hq' := (h.right_iff j k (Ne.symm hkj) hj.1 hj.2.1 hj.2.2 hka hkb hkc).mpr hg.2
    apply h.outer_saturation j k i hj.1 hj.2.1 hka hkb hi.1 hi.2.1 hij (Ne.symm hki) hp hq' ht
    have he : quad a i j k=quad a j k i := by
      apply Fin.ext; dsimp [quad,triple,pair,vxor]; ac_rfl
    exact he ▸ hq

theorem missing_triple_cover (i j : Coord) (hij : i≠j)
    (hG : ({i,j}:Finset Coord)∈h.G) :
    ∀w,InPath p w → Adj (triple a i j) w →
      ∃k,k≠a ∧ k≠b ∧ k≠i ∧ k≠j ∧ w=quad a i j k := by
  have hi := h.avoids _ hG i (by simp)
  have hj := h.avoids _ hG j (by simp)
  intro w hw hadj
  obtain ⟨k,rfl⟩ := neighbor_triple a i j hadj
  by_cases hka : k=a
  · subst k
    rw [quad_cancel_first] at hw
    exact False.elim ((h.left_iff i j hij hi.1 hi.2.1 hi.2.2 hj.1 hj.2.1 hj.2.2).mp hw hG)
  by_cases hki : k=i
  · subst k
    rw [quad_cancel_second] at hw
    exact False.elim (h.absent_pair_a j hj.1 hj.2.1 hw)
  by_cases hkj : k=j
  · subst k
    rw [quad_cancel_third] at hw
    exact False.elim (h.absent_pair_a i hi.1 hi.2.1 hw)
  by_cases hkb : k=b
  · subst k
    have he : quad a i j b=quad a b i j := by
      apply Fin.ext; dsimp [quad,triple,pair,vxor]; ac_rfl
    exact False.elim ((h.right_iff i j hij hi.1 hi.2.1 hi.2.2 hj.1 hj.2.1 hj.2.2).mp (he ▸ hw) hG)
  exact ⟨k,hka,hkb,hki,hkj,rfl⟩

theorem missing_triple_low (f : MissingAtNeighbor p a b) (hFcard : f.F.card=2)
    (i j : Coord) (hij : i≠j) (hG : ({i,j}:Finset Coord)∈h.G)
    (ht : InPath p (triple a i j)) : AtMostOneNeighbor p (triple a i j) := by
  have hi := h.avoids _ hG i (by simp)
  have hj := h.avoids _ hG j (by simp)
  by_cases hex : ∃k,k≠a ∧ k≠b ∧ k≠c ∧ k≠i ∧ k≠j ∧ InPath p (quad a i j k)
  · obtain ⟨k,hka,hkb,hkc,hki,hkj,hq⟩ := hex
    have hm := h.extension_missing f i j k hij hG hka hkb hkc hki hkj hq
    have hedge : ({i,k}:Finset Coord)≠{j,k} := by
      intro he
      have hh : i=j ∨ i=k := by have hh : i∈({j,k}:Finset Coord) := he ▸ (by simp : i∈({i,k}:Finset Coord)); simpa using hh
      exact hh.elim hij (Ne.symm hki)
    have hF : f.F={{i,k},{j,k}} := by
      symm
      apply Finset.eq_of_subset_of_card_le
      · intro s hs
        simp only [Finset.mem_insert,Finset.mem_singleton] at hs
        rcases hs with rfl | rfl
        · exact hm.1
        · exact hm.2
      · simpa [hedge] using hFcard.le
    have hci : ({c,i}:Finset Coord)∉f.F := by
      intro hm
      rw [hF] at hm
      simp only [Finset.mem_insert,Finset.mem_singleton] at hm
      rcases hm with he | he
      · have hh : c=i ∨ c=k := by have hh : c∈({i,k}:Finset Coord) := he ▸ (by simp : c∈({c,i}:Finset Coord)); simpa using hh
        exact hh.elim (Ne.symm hi.2.2) (Ne.symm hkc)
      · have hh : c=j ∨ c=k := by have hh : c∈({j,k}:Finset Coord) := he ▸ (by simp : c∈({c,i}:Finset Coord)); simpa using hh
        exact hh.elim (Ne.symm hj.2.2) (Ne.symm hkc)
    have hcj : ({c,j}:Finset Coord)∉f.F := by
      intro hm
      rw [hF] at hm
      simp only [Finset.mem_insert,Finset.mem_singleton] at hm
      rcases hm with he | he
      · have hh : c=i ∨ c=k := by have hh : c∈({i,k}:Finset Coord) := he ▸ (by simp : c∈({c,j}:Finset Coord)); simpa using hh
        exact hh.elim (Ne.symm hi.2.2) (Ne.symm hkc)
      · have hh : c=j ∨ c=k := by have hh : c∈({j,k}:Finset Coord) := he ▸ (by simp : c∈({c,j}:Finset Coord)); simpa using hh
        exact hh.elim (Ne.symm hj.2.2) (Ne.symm hkc)
    have hti := (f.selected_iff c i (Ne.symm hi.2.2) (Ne.symm h.hac) (Ne.symm h.hbc) hi.1 hi.2.1).mpr hci
    have htj := (f.selected_iff c j (Ne.symm hj.2.2) (Ne.symm h.hac) (Ne.symm h.hbc) hj.1 hj.2.1).mpr hcj
    have hqc : ¬InPath p (quad a i j c) :=
      ordinary_quad_absent p a i j c (Ne.symm hi.1) (Ne.symm hij) (Ne.symm hi.2.2) hj.2.2
        ht (by simpa only [triple_swap a c i] using hti) (by simpa only [triple_swap a c j] using htj)
    have unique (w : Vertex) (hw : InPath p w) (hadj : Adj (triple a i j) w) : w=quad a i j k := by
      obtain ⟨l,hla,hlb,hli,hlj,rfl⟩ := h.missing_triple_cover i j hij hG w hw hadj
      by_cases hlc : l=c
      · subst l; exact False.elim (hqc hw)
      have hl := (h.extension_missing f i j l hij hG hla hlb hlc hli hlj hw).1
      rw [hF] at hl
      simp only [Finset.mem_insert,Finset.mem_singleton] at hl
      have hlk : l=k := by
        rcases hl with he | he
        · have hh : l=i ∨ l=k := by have hh : l∈({i,k}:Finset Coord) := he ▸ (by simp : l∈({i,l}:Finset Coord)); simpa using hh
          exact hh.resolve_left hli
        · have hh : l=j ∨ l=k := by have hh : l∈({j,k}:Finset Coord) := he ▸ (by simp : l∈({i,l}:Finset Coord)); simpa using hh
          exact hh.resolve_left hlj
      rw [hlk]
    intro x y hx hy hax hay
    exact (unique x hx hax).trans (unique y hy hay).symm
  · have unique (w : Vertex) (hw : InPath p w) (hadj : Adj (triple a i j) w) : w=quad a i j c := by
      obtain ⟨k,hka,hkb,hki,hkj,rfl⟩ := h.missing_triple_cover i j hij hG w hw hadj
      by_cases hkc : k=c
      · rw [hkc]
      · exact False.elim (hex ⟨k,hka,hkb,hkc,hki,hkj,hw⟩)
    intro x y hx hy hax hay
    exact (unique x hx hax).trans (unique y hy hay).symm

theorem middle_family_eq (f : MissingAtNeighbor p a b) (hFcard : f.F.card=2) : f.F=h.G := by
  have hs : h.G⊆f.F := by
    intro s hs
    obtain ⟨i,j,hij,rfl⟩ := Finset.card_eq_two.mp (h.edge_card s hs)
    have hi := h.avoids _ hs i (by simp)
    have hj := h.avoids _ hs j (by simp)
    by_contra hn
    have ht := (f.selected_iff i j hij hi.1 hi.2.1 hj.1 hj.2.1).mpr hn
    exact h.triple_not_low i j hi.1 hj.1 ht (h.missing_triple_low f hFcard i j hij hs ht)
  have hc := h.Gcard
  exact (Finset.eq_of_subset_of_card_le hs (by omega)).symm

theorem isolated_forces_c_pair (f : MissingAtNeighbor p a b) (hF : f.F=h.G)
    (z : Coord) (hza : z≠a) (hzb : z≠b) (hzc : z≠c)
    (hz : ∀s∈h.G,z∉s) : InPath p (pair c z) := by
  have hcz : ({c,z}:Finset Coord)∉f.F := by
    rw [hF]
    intro hm
    exact (h.avoids _ hm c (by simp)).2.2 rfl
  have ht := (f.selected_iff c z (Ne.symm hzc) (Ne.symm h.hac) (Ne.symm h.hbc) hza hzb).mpr hcz
  have hnl := h.triple_not_low c z (Ne.symm h.hac) hza ht
  have hcvr : ∀w,InPath p w → Adj (triple a c z) w → w=pair c z ∨ w=quad a b c z := by
    intro w hw hadj
    obtain ⟨k,rfl⟩ := neighbor_triple a c z hadj
    by_cases hka : k=a
    · subst k; exact Or.inl (quad_cancel_first _ _ _)
    by_cases hkc : k=c
    · subst k; rw [quad_cancel_second] at hw
      exact False.elim (h.absent_pair_a z hza hzb hw)
    by_cases hkz : k=z
    · subst k; rw [quad_cancel_third] at hw
      exact False.elim (h.absent_pair_a c (Ne.symm h.hac) (Ne.symm h.hbc) hw)
    by_cases hkb : k=b
    · subst k; right
      apply Fin.ext; dsimp [quad,triple,pair,vxor]; ac_rfl
    have hzk : ({z,k}:Finset Coord)∉h.G := fun hm => hz _ hm (by simp)
    have hp := (h.left_iff z k (Ne.symm hkz) hza hzb hzc hka hkb hkc).mpr hzk
    have hq := (h.right_iff z k (Ne.symm hkz) hza hzb hzc hka hkb hkc).mpr hzk
    have hta := (f.selected_iff z k (Ne.symm hkz) hza hzb hka hkb).mpr (by simpa only [hF] using hzk)
    apply False.elim
    apply h.outer_saturation z k c hza hzb hka hkb (Ne.symm h.hac) (Ne.symm h.hbc)
      (Ne.symm hzc) (Ne.symm hkc) hp hq hta
    have he : quad a c z k=quad a z k c := by
      apply Fin.ext; dsimp [quad,triple,pair,vxor]; ac_rfl
    exact he ▸ hw
  exact (force_two_neighbors p (triple a c z) (pair c z) (quad a b c z) hnl hcvr).1

theorem middle_matching_impossible (f : MissingAtNeighbor p a b) (hFcard : f.F.card=2) : False := by
  have hF := h.middle_family_eq f hFcard
  have hcu := h.isolated_forces_c_pair f hF h.u h.hu.1 h.hu.2.1 h.hu.2.2 h.isolated_u
  have hcv := h.isolated_forces_c_pair f hF h.v h.hv.1 h.hv.2.1 h.hv.2.2 h.isolated_v
  rcases selected_three_neighbors_repeat p h.hc h.h0 hcu hcv
    (adj_symmetric ((adj_zero_iff _).mpr ⟨c,rfl⟩)) (unit_pair_adj c h.u) (unit_pair_adj c h.v)
    with he | he | he
  · exact pair_nonzero c h.u (Ne.symm h.hu.2.2) he.symm
  · exact pair_nonzero c h.v (Ne.symm h.hv.2.2) he.symm
  · exact h.huv (pair_injective_right c h.u h.v he)

end MiddleMatchingConfig
#print axioms MiddleMatchingConfig.middle_family_eq
#print axioms MiddleMatchingConfig.middle_matching_impossible
end
end Snake9
