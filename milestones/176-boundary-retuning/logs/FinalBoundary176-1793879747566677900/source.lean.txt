import BoundaryPacking175
import Uniform15Arithmetic176

open scoped BigOperators
namespace Snake9.Boundary175
open SquareIncidence Count171 Integration172

theorem upper_234_of_weaker_window_potential {m : Nat} (p : Snake m) (hm : 8≤m)
    (b share demand : Nat → Nat)
    (htrunc : ∀ i, ∀ hi : i<m-8,b i≤localAlpha p ⟨8+i,by omega⟩)
    (hshare : ∀ i,∀ hi : i<m+1,share i=shareN 12 p (p.vertex ⟨i,hi⟩))
    (hlocal : ∀ r<m-8,demand r≤∑ k ∈ Finset.range 5,share (r+k+4))
    (hpotential : 4453*(m-8) ≤
      9*(∑ r ∈ Finset.range (m-8),(120*b r+demand r))+5384) : m≤234 := by
  have hp := actual_charge_packing p hm b share demand htrunc hshare hlocal
  have hb := charge_budget_with_loss p (by omega)
  exact (Uniform15Arithmetic176.comparison m _ _ _ hm hb hp hpotential).2

#print axioms upper_234_of_weaker_window_potential
end Snake9.Boundary175
