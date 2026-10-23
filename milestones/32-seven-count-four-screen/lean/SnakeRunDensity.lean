import SnakeCoverage
import RunDensity

namespace Snake9.FourRun
open Snake9 Snake9.LocalWindow Finset

theorem snake_density_of_refuted
    (hall : ∀ cs ∈ patterns, Refuted (winOf cs) (boundsOf (List.replicate 6 4)))
    {m : Nat} (p : Snake m) :
    (m-1)/6 ≤ ((range (m-1)).filter (fun j => coreAlpha p (j+1) ≠ 4)).card := by
  apply density_of_no_six
  intro r hr
  by_contra! hc
  exact no_six_fours_of_refuted hall p r (by omega) hc

#print axioms snake_density_of_refuted
end Snake9.FourRun
