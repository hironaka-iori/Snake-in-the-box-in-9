import Mathlib.Tactic
namespace Snake9.Target7302Pressure

theorem conditional_integer_bound (m W : Nat) (hm : 8 ≤ m)
    (hbudget : W+4200*m ≤ 1098960)
    (hpotential : 9259*(m-8) ≤ 19*W+11301) : m ≤ 235 := by
  omega

theorem mean_alone_insufficient (p d R : ℚ) (hd : 0 ≤ d) (hR : 0 ≤ R)
    (hcycle : 19*p ≤ 9259*d) : ¬ 111960*d+R < 227*p := by
  linarith

theorem threshold_deficit : (111960*19-227*9259 : Nat) = 25447 := by decide

#print axioms conditional_integer_bound
#print axioms mean_alone_insufficient
#print axioms threshold_deficit
end Snake9.Target7302Pressure
