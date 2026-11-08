import BoundaryPacking175
import SingleCritical184

open scoped BigOperators
namespace Snake9.SingleCritical184
open SquareIncidence Count171 Integration172 Boundary175

theorem actual_upper234 {m : Nat} (p : Snake m)
    (b share demand : Nat → Nat)
    (htrunc : ∀ i, ∀ hi : i<m-8,b i≤localAlpha p ⟨8+i,by omega⟩)
    (hshare : ∀ i,∀ hi : i<m+1,share i=shareN 12 p (p.vertex ⟨i,hi⟩))
    (hlocal : ∀ r<m-8,demand r≤∑ k ∈ Finset.range 5,share (r+k+4))
    (hpotential : 4454*(m-8)≤9*(∑ r ∈ Finset.range (m-8),(120*b r+demand r))+5421) :
    m≤234 := by
  by_cases hm : 8≤m
  · have hp := actual_charge_packing p hm b share demand htrunc hshare hlocal
    have hb := charge_budget_with_loss p (by omega)
    exact _root_.SingleCritical184.upper234 m _ _ _ hm hb hp hpotential
  · omega

#print axioms actual_upper234
end Snake9.SingleCritical184
