import NormalizeThreeCenters
import DistinctOuterMirror

namespace Snake9
open SquareIncidence Finset Classical
noncomputable section
set_option maxHeartbeats 1800000

structure DistinctThreeTwosConfig {m : Nat} (p : Snake m) where
  a : Coord
  b : Coord
  c : Coord
  d : Coord
  outer : DistinctOuterConfig p a b c d
  middle : MissingAtNeighbor p a b
  middle_card : middle.F.card=2

theorem NormalizedThreeCenters.to_distinct_config {m : Nat} {p : Snake m}
    {i j k : Fin (m+1)} (h : NormalizedThreeCenters p i j k) (hcd : h.c≠h.d)
    (hai : localAlpha p i=2) (haj : localAlpha p j=2) (hak : localAlpha p k=2) :
    Nonempty (DistinctThreeTwosConfig p) := by
  have h0 : InPath p 0 := ⟨i,h.left_eq⟩
  have ha : InPath p (unit h.a) := ⟨j,h.middle_eq⟩
  have habs : InPath p (pair h.a h.b) := ⟨k,h.right_eq⟩
  obtain ⟨left⟩ := twoMissingAtZero_of_alpha p h.a h.c i h.left_eq hai ha h.before_selected h.hac
  let q := translate p (pair h.a h.b)
  have hqk : q.vertex k=0 := by change vxor (pair h.a h.b) (p.vertex k)=0; rw [h.right_eq,vxor_self]
  have hqa : localAlpha q k=2 := (localAlpha_translate p _ k).trans hak
  have hqb : InPath q (unit h.b) := by
    rw [inPath_translate_at]
    change InPath p (triple h.a h.b h.b)
    simpa only [triple_cancel_right] using ha
  have hqd : InPath q (unit h.d) := (inPath_translate_at p _ _).mpr h.after_selected
  obtain ⟨right⟩ := twoMissingAtZero_of_alpha q h.b h.d k hqk hqa hqb hqd (Ne.symm h.hdb)
  let outer : DistinctOuterConfig p h.a h.b h.c h.d :=
    ⟨h.hab,h.hac,Ne.symm h.hda,h.hbc,Ne.symm h.hdb,hcd,h0,ha,h.before_selected,
      habs,h.after_selected,left,right⟩
  have hza : InPath (translate p (unit h.a)) (unit h.a) :=
    (translate_unit_membership p h.a h.a).mpr (by simpa only [pair_self] using h0)
  have hzb : InPath (translate p (unit h.a)) (unit h.b) := (translate_unit_membership p h.a h.b).mpr habs
  have hz0 : InPath (translate p (unit h.a)) 0 :=
    (inPath_translate_at p _ _).mpr (by simpa using ha)
  obtain ⟨f,hf⟩ := missingAtNeighbor_of_alpha p h.a h.b j h.middle_eq hza hzb
    (unit_cover_two _ h.a h.b hz0 hza hzb h.hab)
  exact ⟨⟨h.a,h.b,h.c,h.d,outer,f,hf.trans haj⟩⟩

theorem normalize_three_twos {m : Nat} (p : Snake m) (r : Nat) (hr : r+4≤m)
    (h1 : localAlpha p ⟨r+1,by omega⟩=2)
    (h2 : localAlpha p ⟨r+2,by omega⟩=2)
    (h3 : localAlpha p ⟨r+3,by omega⟩=2) :
    Nonempty (DistinctThreeTwosConfig (translate p (p.vertex ⟨r+1,by omega⟩))) := by
  obtain ⟨h,hcd⟩ := normalize_three_twos_to_distinct_window p r hr h1 h2 h3
  exact h.to_distinct_config hcd
    ((localAlpha_translate p _ _).trans h1)
    ((localAlpha_translate p _ _).trans h2)
    ((localAlpha_translate p _ _).trans h3)

theorem DistinctOuterConfig.remaining_double_delta_cases {m : Nat} {p : Snake m} {a b c d : Coord}
    (h : DistinctOuterConfig p a b c d) (f : MissingAtNeighbor p a b) (hFcard : f.F.card=2) :
    (∃e : Coord,e∈distinctR a b c d ∧
      h.left.F={{b,d},{b,e}} ∧ h.right.F={{a,c},{a,e}}) ∨
    (∃s t : Finset Coord,s.card=2 ∧ t.card=2 ∧
      s⊆insert d (distinctR a b c d) ∧ t⊆insert c (distinctR a b c d) ∧
      b∉s ∧ a∉t ∧ h.left.F=insert {b,d} {s} ∧ h.right.F=insert {a,c} {t}) := by
  by_cases hbd : ({b,d}:Finset Coord)∈h.left.F
  · by_cases hac : ({a,c}:Finset Coord)∈h.right.F
    · exact h.double_delta_cases hbd hac
    · exact False.elim (h.single_delta_impossible hbd hac f hFcard)
  · by_cases hac : ({a,c}:Finset Coord)∈h.right.F
    · exact False.elim (h.opposite_delta_impossible hbd hac f hFcard)
    · exact False.elim (h.zero_delta_impossible hbd hac)

#print axioms normalize_three_twos
#print axioms DistinctOuterConfig.remaining_double_delta_cases
end
end Snake9
