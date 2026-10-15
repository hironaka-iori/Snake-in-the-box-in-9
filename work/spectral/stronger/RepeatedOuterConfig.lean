import GeneralMissingFamily
import OuterMatchingCount
import FiniteEndpointCounting

namespace Snake9
open SquareIncidence Finset Classical
noncomputable section
set_option maxHeartbeats 1500000

structure TwoMissingAtZero {m : Nat} (p : Snake m) (x y : Coord) where
  F : Finset (Finset Coord)
  Fcard : F.card=2
  edge_card : ∀s∈F,s.card=2
  avoids : ∀s∈F,∀k∈s,k≠x ∧ k≠y
  selected_iff : ∀i j : Coord,i≠j→i≠x→i≠y→j≠x→j≠y→
    (InPath p (pair i j) ↔ ({i,j}:Finset Coord)∉F)

theorem twoMissingAtZero_of_alpha {m : Nat} (p : Snake m) (x y : Coord)
    (i : Fin (m+1)) (hi : p.vertex i=0) (ha : localAlpha p i=2)
    (hx : InPath p (unit x)) (hy : InPath p (unit y)) (hxy : x≠y) :
    Nonempty (TwoMissingAtZero p x y) := by
  have h0 : InPath p 0 := ⟨i,hi⟩
  have cover := unit_cover_two p x y h0 hx hy hxy
  refine ⟨⟨missingPairSupports p,(missingPairSupports_card p i hi).trans ha,
    missingPairSupports_edge_card p,?_,?_⟩⟩
  · exact fun s hs k hk => ⟨missingPairSupports_avoids_selected_unit p x hx s hs k hk,
      missingPairSupports_avoids_selected_unit p y hy s hs k hk⟩
  · intro j k hjk hjx hjy hkx hky
    have hj : ¬InPath p (unit j) := by
      intro h
      rcases cover j h with h | h
      · exact hjx h
      · exact hjy h
    have hk : ¬InPath p (unit k) := by
      intro h
      rcases cover k h with h | h
      · exact hkx h
      · exact hky h
    have he := mem_missingPairSupports_iff p h0 j k hjk
    simp only [hj,hk,not_false_eq_true,true_and] at he
    rw [he]
    exact not_not.symm

/-- Outer centers of the window `c,0,a,ab,abc`, each of count two. -/
structure RepeatedOuterConfig {m : Nat} (p : Snake m) (a b c : Coord) where
  hab : a≠b
  hac : a≠c
  hbc : b≠c
  hzero : InPath p 0
  ha : InPath p (unit a)
  hc : InPath p (unit c)
  hab_selected : InPath p (pair a b)
  habc_selected : InPath p (triple a b c)
  left : TwoMissingAtZero p a c
  right : TwoMissingAtZero (translate p (pair a b)) b c

def repeatedR (a b c : Coord) : Finset Coord := Finset.univ\{a,b,c}

theorem mem_repeatedR (a b c k : Coord) : k∈repeatedR a b c ↔ k≠a ∧ k≠b ∧ k≠c := by
  simp [repeatedR]

theorem translated_pair_quad (p : Snake m) (a b i j : Coord) :
    InPath (translate p (pair a b)) (pair i j) ↔ InPath p (quad a b i j) := by
  rw [inPath_translate_at]
  have he : vxor (pair a b) (pair i j)=quad a b i j := by
    exact (vxor_assoc _ _ _).symm
  rw [he]

namespace RepeatedOuterConfig
variable {m : Nat} {p : Snake m} {a b c : Coord} (h : RepeatedOuterConfig p a b c)
include h

theorem cover_left : ∀k,InPath p (unit k)→k=a ∨ k=c :=
  unit_cover_two p a c h.hzero h.ha h.hc h.hac

theorem cover_right : ∀k,InPath (translate p (pair a b)) (unit k)→k=b ∨ k=c := by
  have h0 : InPath (translate p (pair a b)) 0 := by
    rw [inPath_translate_at,vxor_zero]
    exact h.hab_selected
  have hb : InPath (translate p (pair a b)) (unit b) := by
    rw [inPath_translate_at]
    change InPath p (triple a b b)
    simpa only [triple_cancel_right] using h.ha
  have hc : InPath (translate p (pair a b)) (unit c) := by
    rw [inPath_translate_at]
    exact h.habc_selected
  exact unit_cover_two _ b c h0 hb hc h.hbc

theorem absent_unit (k : Coord) (hka : k≠a) (hkc : k≠c) : ¬InPath p (unit k) := by
  intro hk
  rcases h.cover_left k hk with he | he
  · exact hka he
  · exact hkc he

theorem absent_abk (k : Coord) (hkb : k≠b) (hkc : k≠c) :
    ¬InPath p (triple a b k) := by
  intro hk
  have hz : InPath (translate p (pair a b)) (unit k) := (inPath_translate_at p _ _).mpr hk
  rcases h.cover_right k hz with he | he
  · exact hkb he
  · exact hkc he

theorem right_pair_iff (i j : Coord) (hij : i≠j) (hib : i≠b) (hic : i≠c)
    (hjb : j≠b) (hjc : j≠c) :
    InPath p (quad a b i j) ↔ ({i,j}:Finset Coord)∉h.right.F := by
  rw [←translated_pair_quad]
  exact h.right.selected_iff i j hij hib hic hjb hjc

theorem same_hole (k : Coord) (hk : k∈repeatedR a b c) :
    ({b,k}:Finset Coord)∈h.left.F ↔ ({a,k}:Finset Coord)∈h.right.F := by
  obtain ⟨hka,hkb,hkc⟩ := (mem_repeatedR a b c k).mp hk
  have hl := h.left.selected_iff b k (Ne.symm hkb) (Ne.symm h.hab) h.hbc hka hkc
  have hr := h.right_pair_iff a k (Ne.symm hka) h.hab h.hac hkb hkc
  have he : quad a b a k=pair b k := by rw [quad_swap_last,quad_cancel_first]
  rw [he] at hr
  exact not_iff_not.mp (hl.symm.trans hr)

end RepeatedOuterConfig

#print axioms twoMissingAtZero_of_alpha
#print axioms RepeatedOuterConfig.same_hole
end
end Snake9
