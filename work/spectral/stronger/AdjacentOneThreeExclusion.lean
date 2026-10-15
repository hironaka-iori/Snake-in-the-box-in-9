import OneThreeExclusion
import UpperBound248

namespace Snake9
open SquareIncidence

theorem adjacent_internal_one_three_impossible {m : Nat} (p : Snake m)
    (i j : Fin (m+1)) (hi0 : 0 < i.val) (him : i.val < m)
    (hj0 : 0 < j.val) (hjm : j.val < m) (hadj : Adj (p.vertex i) (p.vertex j)) :
    ¬ (localAlpha p i=1 ∧ localAlpha p j=3) := by
  rintro ⟨hi,hj⟩
  obtain ⟨config⟩ := missingConfig_of_adjacent_internal p i j hi0 him hj0 hjm hadj hi
  exact config.root.three_missing_impossible config.missing (config.Fcard.trans hj)

theorem alpha_one_internal_neighbor_ge_four {m : Nat} (p : Snake m)
    (i j : Fin (m+1)) (hi0 : 0 < i.val) (him : i.val < m)
    (hj0 : 0 < j.val) (hjm : j.val < m) (hadj : Adj (p.vertex i) (p.vertex j))
    (hi : localAlpha p i=1) : 4≤localAlpha p j := by
  have hp := localAlpha_positive p j
  have h1 := adjacent_internal_alpha_one_impossible p i j hi0 him hj0 hjm hadj
  have h2 := adjacent_internal_one_two_impossible p i j hi0 him hj0 hjm hadj
  have h3 := adjacent_internal_one_three_impossible p i j hi0 him hj0 hjm hadj
  omega

#print axioms adjacent_internal_one_three_impossible
#print axioms alpha_one_internal_neighbor_ge_four
end Snake9
