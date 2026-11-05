import UpperBound245
import BoundaryArithmetic175

namespace Snake9.Boundary175
open SquareIncidence
open scoped BigOperators

-- The bound concerns actual singleton-square counts along a cube snake.
theorem seven_internal_at_least_sixteen {m : Nat} (p : Snake m) (hm : 8 ≤ m) :
    16 ≤ localAlpha p ⟨1,by omega⟩ + localAlpha p ⟨2,by omega⟩ +
      localAlpha p ⟨3,by omega⟩ + localAlpha p ⟨4,by omega⟩ +
      localAlpha p ⟨5,by omega⟩ + localAlpha p ⟨6,by omega⟩ +
      localAlpha p ⟨7,by omega⟩ := by
  let a : Nat → Nat := fun k => if hk : k < m+1 then localAlpha p ⟨k,hk⟩ else 0
  have ha (k : Nat) (hk : k ≤ m) : a k = localAlpha p ⟨k,by omega⟩ := by
    simp [a, show k<m+1 by omega]
  have hp (k : Nat) (hk : k ≤ 7) : 1 ≤ a k := by
    rw [ha k (by omega)]
    exact localAlpha_positive p _
  have hone (k : Nat) (hk : k ≤ 6) :
      (a k=1 → 4≤a (k+1)) ∧ (a (k+1)=1 → 4≤a k) := by
    rw [ha k (by omega),ha (k+1) (by omega)]
    have hadj : Adj (p.vertex ⟨k,by omega⟩) (p.vertex ⟨k+1,by omega⟩) :=
      (path_adj_iff p _ _).mpr (Or.inl rfl)
    exact ⟨alpha_one_neighbor_ge_four p (by omega) _ _ hadj,
      alpha_one_neighbor_ge_four p (by omega) _ _ (adj_symmetric hadj)⟩
  have hno (k : Nat) (hk : k ≤ 4) : ¬(a (k+1)=2 ∧ a (k+2)=2 ∧ a (k+3)=2) := by
    rw [ha (k+1) (by omega),ha (k+2) (by omega),ha (k+3) (by omega)]
    exact no_three_consecutive_internal_twos p k (by omega)
  have h := BoundaryArithmetic175.seven_count_minimum
    (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7)
    ⟨hp 1 (by omega),hp 2 (by omega),hp 3 (by omega),hp 4 (by omega),
      hp 5 (by omega),hp 6 (by omega),hp 7 (by omega)⟩
    (hone 1 (by omega)) (hone 2 (by omega)) (hone 3 (by omega))
    (hone 4 (by omega)) (hone 5 (by omega)) (hone 6 (by omega))
    (hno 0 (by omega)) (hno 1 (by omega)) (hno 2 (by omega))
    (hno 3 (by omega)) (hno 4 (by omega))
  simpa only [ha 1 (by omega),ha 2 (by omega),ha 3 (by omega),ha 4 (by omega),
    ha 5 (by omega),ha 6 (by omega),ha 7 (by omega)] using h

#print axioms seven_internal_at_least_sixteen
end Snake9.Boundary175
