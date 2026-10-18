import First112Complete

namespace Snake9.Regrowth.First112
theorem region_exclusion (q : Snake 81) (h : Conditions q) : False :=
  Dfs112FirstBoolean.constraints_unsat (valuation q) (all_constraints q h)
#print axioms region_exclusion
end Snake9.Regrowth.First112
