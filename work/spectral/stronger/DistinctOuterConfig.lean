import RepeatedOuterGeometry
import PairFamilySplitting

namespace Snake9
open SquareIncidence Finset Classical
noncomputable section
set_option maxHeartbeats 1500000

/-- Outer centers of the window `c,0,a,ab,abd`, with four distinct coordinates. -/
structure DistinctOuterConfig {m : Nat} (p : Snake m) (a b c d : Coord) where
  hab : a≠b
  hac : a≠c
  had : a≠d
  hbc : b≠c
  hbd : b≠d
  hcd : c≠d
  hzero : InPath p 0
  ha : InPath p (unit a)
  hc : InPath p (unit c)
  hab_selected : InPath p (pair a b)
  habd_selected : InPath p (triple a b d)
  left : TwoMissingAtZero p a c
  right : TwoMissingAtZero (translate p (pair a b)) b d

def distinctR (a b c d : Coord) : Finset Coord := Finset.univ\{a,b,c,d}

theorem mem_distinctR (a b c d k : Coord) :
    k∈distinctR a b c d ↔ k≠a ∧ k≠b ∧ k≠c ∧ k≠d := by simp [distinctR]

namespace DistinctOuterConfig
variable {m : Nat} {p : Snake m} {a b c d : Coord} (h : DistinctOuterConfig p a b c d)
include h

theorem cover_left : ∀k,InPath p (unit k)→k=a ∨ k=c :=
  unit_cover_two p a c h.hzero h.ha h.hc h.hac

theorem cover_right : ∀k,InPath (translate p (pair a b)) (unit k)→k=b ∨ k=d := by
  have h0 : InPath (translate p (pair a b)) 0 := by
    rw [inPath_translate_at,vxor_zero]
    exact h.hab_selected
  have hb : InPath (translate p (pair a b)) (unit b) := by
    rw [inPath_translate_at]
    change InPath p (triple a b b)
    simpa only [triple_cancel_right] using h.ha
  have hd : InPath (translate p (pair a b)) (unit d) :=
    (inPath_translate_at p _ _).mpr h.habd_selected
  exact unit_cover_two _ b d h0 hb hd h.hbd

theorem absent_unit (k : Coord) (hka : k≠a) (hkc : k≠c) : ¬InPath p (unit k) := by
  intro hk
  rcases h.cover_left k hk with he | he
  · exact hka he
  · exact hkc he

theorem absent_abk (k : Coord) (hkb : k≠b) (hkd : k≠d) :
    ¬InPath p (triple a b k) := by
  intro hk
  have hz : InPath (translate p (pair a b)) (unit k) := (inPath_translate_at p _ _).mpr hk
  rcases h.cover_right k hz with he | he
  · exact hkb he
  · exact hkd he

theorem right_pair_iff (i j : Coord) (hij : i≠j) (hib : i≠b) (hid : i≠d)
    (hjb : j≠b) (hjd : j≠d) :
    InPath p (quad a b i j) ↔ ({i,j}:Finset Coord)∉h.right.F := by
  rw [←translated_pair_quad]
  exact h.right.selected_iff i j hij hib hid hjb hjd

theorem same_hole (k : Coord) (hk : k∈distinctR a b c d) :
    ({b,k}:Finset Coord)∈h.left.F ↔ ({a,k}:Finset Coord)∈h.right.F := by
  obtain ⟨hka,hkb,hkc,hkd⟩ := (mem_distinctR a b c d k).mp hk
  have hl := h.left.selected_iff b k (Ne.symm hkb) (Ne.symm h.hab) h.hbc hka hkc
  have hr := h.right_pair_iff a k (Ne.symm hka) h.hab h.had hkb hkd
  have he : quad a b a k=pair b k := by rw [quad_swap_last,quad_cancel_first]
  rw [he] at hr
  exact not_iff_not.mp (hl.symm.trans hr)

theorem row_neighbor_cover (k : Coord) (hk : k∈distinctR a b c d)
    (w : Vertex) (hw : InPath p w) (hadj : Adj (pair b k) w) :
    w=triple b k c ∨ w=triple b k d ∨
      ∃l,l∈distinctR a b c d ∧ l≠k ∧ w=triple b k l := by
  obtain ⟨hka,hkb,hkc,hkd⟩ := (mem_distinctR a b c d k).mp hk
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
    exact False.elim (h.absent_abk k hkb hkd hw)
  by_cases hlc : l=c
  · subst l
    exact Or.inl rfl
  by_cases hld : l=d
  · subst l
    exact Or.inr (Or.inl rfl)
  exact Or.inr (Or.inr ⟨l,(mem_distinctR a b c d l).mpr ⟨hla,hlb,hlc,hld⟩,hlk,rfl⟩)

end DistinctOuterConfig

#print axioms DistinctOuterConfig.same_hole
#print axioms DistinctOuterConfig.row_neighbor_cover
end
end Snake9
