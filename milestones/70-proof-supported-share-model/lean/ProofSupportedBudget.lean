import PairBasis4911
import CheckedShareBudget

namespace Snake9.ProofSupported70

/-- This is an application of the existing pair theorem, not a new exclusion
    requiring another SAT refutation. Counts at other positions are unrestricted. -/
theorem two_ones_impossible {m : Nat} (p : Snake m) (r a b c d e : Nat)
    (hn : [a,b,c,d,e].Nodup) (h9 : ∀ x ∈ [a,b,c,d,e], x<9)
    (hr : r+6 ≤ m)
    (hd : ∀ j, j<6 → LocalWindow.dir p (r+j) =
      ([a,b,c,a,d,e] : List Nat).getD j 0)
    (hfirst : LocalWindow.coreAlpha p (r+1)=1)
    (hfourth : LocalWindow.coreAlpha p (r+4)=1) : False := by
  exact LocalWindow.PairBasis4911.exclusion p r a b c d e hn h9 hr hd
    (by omega) (by omega)

theorem enriched_budget (m W : ℤ)
    (hb : W+4200*m ≤ 1098960)
    (hp : 480*(m-8) ≤ W+578) : 4680*m ≤ 1103378 := by omega

theorem enriched_integer_bound (m : ℤ) (h : 4680*m ≤ 1103378) : m ≤ 235 := by omega

/-- Even zero potential range would not make slope 480 exclude 235. -/
theorem slope_insufficient_for_234 (mu R : ℚ) (hm : mu ≤ 480) (hR : 0 ≤ R) :
    235*(4200+mu) ≤ 1098960+8*mu+R := by linarith

theorem replacement_cycle_average : (480+360+600+480:ℕ)=4*480 := by decide

#print axioms two_ones_impossible
#print axioms enriched_budget
#print axioms enriched_integer_bound
#print axioms slope_insufficient_for_234
#print axioms replacement_cycle_average
end Snake9.ProofSupported70
