import Mathlib.Tactic

namespace Snake9.RelaxedGraph109

theorem completed_comparison_barrier (P R : Int) (hp : P ≤ 483) (hR : 0 ≤ R) :
    (4200+P)*235 ≤ 1098960+8*P+R := by omega

theorem conditional_comparison_barrier (P R : Int) (hp : P ≤ 496) (hR : 0 ≤ R) :
    (4200+P)*234 ≤ 1098960+8*P+R := by omega

#print axioms completed_comparison_barrier
#print axioms conditional_comparison_barrier
end Snake9.RelaxedGraph109
