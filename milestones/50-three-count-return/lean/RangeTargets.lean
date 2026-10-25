import Mathlib.Tactic
namespace Snake9.RangeTargets

/-- Retain empty squares in the already established charge inequality. -/
theorem retained_empty_squares (m T s : Nat)
    (hsquare : T + 2*s + 35*(m+1) = 9214)
    (hcharge : 42*m ≤ 11*T + 203) :
    427*m + 22*s ≤ 101172 := by omega

theorem nineteen_empty_squares (m s : Nat)
    (h : 427*m + 22*s ≤ 101172) (hs : 19 ≤ s) : m ≤ 235 := by omega

theorem empty_square_targets (m s : Nat) (h : 427*m + 22*s ≤ 101172) :
    (38 ≤ s → m ≤ 234) ∧ (58 ≤ s → m ≤ 233) ∧
    (77 ≤ s → m ≤ 232) ∧ (97 ≤ s → m ≤ 231) ∧
    (116 ≤ s → m ≤ 230) := by omega

/-- A design target only: the graph-to-snake premises must be proved separately. -/
theorem mean_four_target (m G W R : Nat) (hm : 7 ≤ m)
    (hglobal : G + 840*(m+1) ≤ 221136)
    (hbudget : W + 2352 ≤ 7*G)
    (hpath : 672*(m-7) ≤ W+R) (hr : R ≤ 1847) : m ≤ 235 := by omega

#print axioms retained_empty_squares
#print axioms nineteen_empty_squares
#print axioms empty_square_targets
#print axioms mean_four_target
end Snake9.RangeTargets
