import BoundaryPacking175
import SmallLossSupport174
import Floor14Optimum178

open scoped BigOperators
namespace Snake9.Floor14Case178
open SquareIncidence Count171 Integration172 Boundary175 SmallLoss174

theorem actual_upper234 {m : Nat} (p : Snake m) (hm : 8≤m)
    (b share demand : Nat → Nat)
    (htrunc : ∀ i, ∀ hi : i<m-8,b i≤localAlpha p ⟨8+i,by omega⟩)
    (hshare : ∀ i,∀ hi : i<m+1,share i=shareN 12 p (p.vertex ⟨i,hi⟩))
    (hlocal : ∀ r<m-8,demand r≤∑ k ∈ Finset.range 5,share (r+k+4))
    (hpotential : 4448*(m-8)≤9*(∑ r ∈ Finset.range (m-8),(120*b r+demand r))+5380)
    (hl : 2≤totalLoss p) : m≤234 := by
  have hp := actual_charge_packing p hm b share demand htrunc hshare hlocal
  have hb := charge_budget_with_loss p (by omega)
  exact Floor14Optimum178.uniform_upper234 m _ _ _ hm hb hp hpotential hl

theorem actual_critical_case {m : Nat} (p : Snake m) (hm : 235≤m)
    (b share demand : Nat → Nat)
    (htrunc : ∀ i, ∀ hi : i<m-8,b i≤localAlpha p ⟨8+i,by omega⟩)
    (hshare : ∀ i,∀ hi : i<m+1,share i=shareN 12 p (p.vertex ⟨i,hi⟩))
    (hlocal : ∀ r<m-8,demand r≤∑ k ∈ Finset.range 5,share (r+k+4))
    (hpotential : 4448*(m-8)≤9*(∑ r ∈ Finset.range (m-8),(120*b r+demand r))+5380) :
    m=235 ∧ (totalLoss p=0 ∨ totalLoss p=1) ∧
    (∀ q : Vertex, ∃ v, InPath p v ∧ Adj q v) ∧
    (positiveLossCorners p).card≤1 := by
  have hp := actual_charge_packing p (by omega) b share demand htrunc hshare hlocal
  have hb := charge_budget_with_loss p (by omega)
  have hc := Floor14Optimum178.critical_zero_or_one m _ _ _ hm hb hp hpotential
  have hl : totalLoss p≤1 := by rcases hc.2 with h | h <;> omega
  have hd := small_loss_dominates p (by omega) (show totalLoss p≤95 by omega)
  have hs := positive_corner_count_le_loss p
  exact ⟨hc.1,hc.2,hd,by omega⟩

#print axioms actual_upper234
#print axioms actual_critical_case
end Snake9.Floor14Case178
