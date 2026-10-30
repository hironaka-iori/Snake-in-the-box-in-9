import ExclusionSelection
import TargetBudget

namespace Snake9.RecoveredRuleBudget71
open Snake9.ExclusionSelection69

/-- Removing already impossible transitions only removes cover obligations. -/
theorem cover_after_pruning {K : Type*} [DecidableEq K]
    (oldClauses newClauses : Finset (Finset K)) (selected : Finset K)
    (hsub : newClauses ⊆ oldClauses) (hc : Covers oldClauses selected) :
    Covers newClauses selected := by
  intro c hcnew
  exact hc c (hsub hcnew)

/-- If the new mandatory keys cover the surviving clauses, the new least cover
    is contained in every old cover, for the same fixed potential and basis. -/
theorem least_cover_after_pruning {K : Type*} [DecidableEq K]
    (oldClauses newClauses : Finset (Finset K)) (oldSelected mandatory : Finset K)
    (hsub : newClauses ⊆ oldClauses) (hc : Covers oldClauses oldSelected)
    (hsingle : ∀ k ∈ mandatory, {k} ∈ newClauses) : mandatory ⊆ oldSelected := by
  intro k hk
  exact singleton_forces (cover_after_pruning _ _ _ hsub hc) (hsingle k hk)

theorem exact_mean_budget (m W : ℤ)
    (hb : W+4200*m ≤ 1098960)
    (hp : 1492*(m-8) ≤ 3*W+1897) : 14092*m ≤ 3310713 := by omega

theorem exact_mean_bound (m : ℤ) (h : 14092*m ≤ 3310713) : m ≤ 234 := by omega

theorem relaxed_new_budget (m W : ℤ)
    (hb : W+4200*m ≤ 1098960)
    (hp : 1489*(m-8) ≤ 3*W+1897) : 14089*m ≤ 3310689 := by omega

theorem relaxed_new_bound (m : ℤ) (h : 14089*m ≤ 3310689) : m ≤ 234 := by omega

theorem smaller_new_numerator_insufficient (p : ℤ) (hp : p ≤ 1488) :
    (p+4200*3)*235 ≤ 1098960*3+8*p+1897 := by omega

/-- Even zero potential range cannot make this mean exclude 234. -/
theorem mean_insufficient_for_233 :
    (1492+4200*3:ℤ)*234 ≤ 1098960*3+8*1492 := by norm_num

#print axioms cover_after_pruning
#print axioms least_cover_after_pruning
#print axioms exact_mean_budget
#print axioms exact_mean_bound
#print axioms relaxed_new_budget
#print axioms relaxed_new_bound
#print axioms smaller_new_numerator_insufficient
#print axioms mean_insufficient_for_233
end Snake9.RecoveredRuleBudget71
