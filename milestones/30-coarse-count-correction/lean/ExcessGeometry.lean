import ExcessArithmetic
import Window2
import Window3

namespace Snake9.CoarseCorrection
open Snake9.LocalWindow

def exactBounds : List (Nat × Nat) := [(6,6),(3,3),(3,3),(6,6),(3,3),(3,3),(6,6)]

theorem pattern_exact_bounds (f : Nat → Nat)
    (h0 : f 0 = 6) (h1 : f 1 = 3) (h2 : f 2 = 3) (h3 : f 3 = 6)
    (h4 : f 4 = 3) (h5 : f 5 = 3) (h6 : f 6 = 6) :
    ∀ i, i < exactBounds.length →
      (exactBounds.getD i (0,21)).1 ≤ f i ∧ f i ≤ (exactBounds.getD i (0,21)).2 := by
  intro i hi
  change i < 7 at hi
  interval_cases i <;> simp [exactBounds, h0, h1, h2, h3, h4, h5, h6]

def counts {m : Nat} (p : Snake m) (r j : Nat) : Nat := coreAlpha p (r+j+1)

/-- In the normalized direction window 01234120, the three high counts
sum to at least nineteen whenever the other four counts equal three. -/
theorem excess_case2 {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+8 ≤ m)
    (hP : ∀ j, j < 8 → P.fwd (dir p (r+j)) = CoarseCount2.directions.getD j 0)
    (h0 : 6 ≤ counts p r 0) (h1 : counts p r 1 = 3) (h2 : counts p r 2 = 3)
    (h3 : 6 ≤ counts p r 3) (h4 : counts p r 4 = 3) (h5 : counts p r 5 = 3)
    (h6 : 6 ≤ counts p r 6) :
    19 ≤ counts p r 0 + counts p r 3 + counts p r 6 := by
  by_contra! h
  have he := high_equal_six _ _ _ h0 h3 h6 (by omega)
  apply CoarseCount2.excluded_in_snake p P r hr hP
  exact pattern_exact_bounds (counts p r) he.1 h1 h2 he.2.1 h4 h5 he.2.2

/-- The same excess conclusion for the normalized direction window 01234125. -/
theorem excess_case3 {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+8 ≤ m)
    (hP : ∀ j, j < 8 → P.fwd (dir p (r+j)) = CoarseCount3.directions.getD j 0)
    (h0 : 6 ≤ counts p r 0) (h1 : counts p r 1 = 3) (h2 : counts p r 2 = 3)
    (h3 : 6 ≤ counts p r 3) (h4 : counts p r 4 = 3) (h5 : counts p r 5 = 3)
    (h6 : 6 ≤ counts p r 6) :
    19 ≤ counts p r 0 + counts p r 3 + counts p r 6 := by
  by_contra! h
  have he := high_equal_six _ _ _ h0 h3 h6 (by omega)
  apply CoarseCount3.excluded_in_snake p P r hr hP
  exact pattern_exact_bounds (counts p r) he.1 h1 h2 he.2.1 h4 h5 he.2.2

#print axioms pattern_exact_bounds
#print axioms excess_case2
#print axioms excess_case3
end Snake9.CoarseCorrection
