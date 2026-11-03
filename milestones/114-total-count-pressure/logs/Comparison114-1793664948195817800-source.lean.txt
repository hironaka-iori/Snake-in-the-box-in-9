import Mathlib.Tactic

/-! Exact slope/range requirements for the existing global comparison. -/
namespace Snake9.Comparison114

theorem exclude235_iff (p d R : Nat) :
    1098960*d+8*p+R < (4200*d+p)*235 ↔ 111960*d+R < 227*p := by
  omega

theorem exclude234_iff (p d R : Nat) :
    1098960*d+8*p+R < (4200*d+p)*234 ↔ 116160*d+R < 226*p := by
  omega

theorem total19_ceiling_allows235 (p d R : Nat) (h : 5*p ≤ 2424*d) :
    (4200*d+p)*235 ≤ 1098960*d+8*p+R := by
  omega

#print axioms exclude235_iff
#print axioms exclude234_iff
#print axioms total19_ceiling_allows235
end Snake9.Comparison114
