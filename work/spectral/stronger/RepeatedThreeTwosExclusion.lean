import RepeatedOuterMatching
import MiddleMatchingGeometry

namespace Snake9
open SquareIncidence Finset Classical
noncomputable section
set_option maxHeartbeats 1800000

theorem repeated_outer_middle_impossible {m : Nat} {p : Snake m} {a b c : Coord}
    (h : RepeatedOuterConfig p a b c) (f : MissingAtNeighbor p a b) (hFcard : f.F.card=2) : False := by
  obtain ⟨G,u,v,hleft,hright,hG2,hC4,hGR,huv,hu,hv,hui,hvi,hbu,hlu,hbv,hlv⟩ := h.outer_matching
  have hedge : ∀s∈G,s.card=2 := by rw [←hleft]; exact h.left.edge_card
  let q : MiddleMatchingConfig p a b c := {
    hab:=h.hab, hac:=h.hac, hbc:=h.hbc,
    h0:=h.hzero, ha:=h.ha, hc:=h.hc,
    hab_selected:=h.hab_selected, habc_selected:=h.habc_selected,
    G:=G, Gcard:=hG2, edge_card:=hedge,
    avoids:=fun s hs k hk => (mem_repeatedR a b c k).mp (hGR s hs hk),
    matching:=pair_family_matching_of_card_union G hG2 hedge hC4,
    left_iff:=by
      intro i j hij hia hib hic hja hjb hjc
      rw [←hleft]
      exact h.left.selected_iff i j hij hia hic hja hjc,
    right_iff:=by
      intro i j hij hia hib hic hja hjb hjc
      rw [←hright]
      exact h.right_pair_iff i j hij hib hic hjb hjc,
    u:=u, v:=v, huv:=huv,
    hu:=(mem_repeatedR a b c u).mp hu,
    hv:=(mem_repeatedR a b c v).mp hv,
    isolated_u:=hui, isolated_v:=hvi,
    hbu:=hbu, hbv:=hbv, low_bu:=hlu, low_bv:=hlv }
  exact q.middle_matching_impossible f hFcard

/-- No actual snake contains the window `c,0,a,ab,abc` with the three
central singleton-square counts all equal to two. -/
theorem repeated_three_twos_impossible {m : Nat} (p : Snake m) (a b c : Coord)
    (hab : a≠b) (hac : a≠c) (hbc : b≠c)
    (i j k : Fin (m+1)) (hi : p.vertex i=0) (hj : p.vertex j=unit a)
    (hk : p.vertex k=pair a b)
    (hci : InPath p (unit c)) (hcj : InPath p (triple a b c))
    (hai : localAlpha p i=2) (haj : localAlpha p j=2) (hak : localAlpha p k=2) : False := by
  have h0 : InPath p 0 := ⟨i,hi⟩
  have ha : InPath p (unit a) := ⟨j,hj⟩
  have habs : InPath p (pair a b) := ⟨k,hk⟩
  obtain ⟨left⟩ := twoMissingAtZero_of_alpha p a c i hi hai ha hci hac
  let q := translate p (pair a b)
  have hqk : q.vertex k=0 := by change vxor (pair a b) (p.vertex k)=0; rw [hk,vxor_self]
  have hqa : localAlpha q k=2 := (localAlpha_translate p _ k).trans hak
  have hqb : InPath q (unit b) := by
    rw [inPath_translate_at]
    change InPath p (triple a b b)
    simpa only [triple_cancel_right] using ha
  have hqc : InPath q (unit c) := (inPath_translate_at p _ _).mpr hcj
  obtain ⟨right⟩ := twoMissingAtZero_of_alpha q b c k hqk hqa hqb hqc hbc
  let h : RepeatedOuterConfig p a b c :=
    ⟨hab,hac,hbc,h0,ha,hci,habs,hcj,left,right⟩
  have hza : InPath (translate p (unit a)) (unit a) :=
    (translate_unit_membership p a a).mpr (by simpa only [pair_self] using h0)
  have hzb : InPath (translate p (unit a)) (unit b) := (translate_unit_membership p a b).mpr habs
  have hz0 : InPath (translate p (unit a)) 0 :=
    (inPath_translate_at p _ _).mpr (by simpa using ha)
  obtain ⟨f,hf⟩ := missingAtNeighbor_of_alpha p a b j hj hza hzb
    (unit_cover_two _ a b hz0 hza hzb hab)
  exact repeated_outer_middle_impossible h f (hf.trans haj)

#print axioms repeated_outer_middle_impossible
#print axioms repeated_three_twos_impossible
end
end Snake9
