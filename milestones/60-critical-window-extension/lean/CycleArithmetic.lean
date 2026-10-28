import Mathlib.Tactic
namespace Snake9.CriticalArithmetic60
theorem cycle_weight : ([366, 726, 365, 490, 729, 240, 248, 734, 725, 125, 604, 720, 600, 120, 720, 720, 240, 240, 720, 480] : List Nat).sum = 9912 := by decide +kernel
theorem insufficient (mu rho : ℚ) (hm : mu≤2478/5) (hr : 0≤rho) :
    235*(4200+mu) ≤ 1099560+9*mu+rho := by linarith
theorem generic_budget (n m G W : ℤ)
    (hg : G+840*(m+1)≤221136) (hw : W+120*(n+6)≤5*G) :
    W+4200*m≤1100760-120*n := by linarith
theorem generic_potential (n m p d W R : ℤ) (hd : 0≤d)
    (hb : W+4200*m≤1100760-120*n)
    (hp : p*(m-(n-1))≤d*W+R) :
    (p+4200*d)*m≤(1100760-120*n)*d+(n-1)*p+R := by
  have := mul_le_mul_of_nonneg_left hb hd
  nlinarith
#print axioms cycle_weight
#print axioms insufficient
#print axioms generic_budget
#print axioms generic_potential
end Snake9.CriticalArithmetic60
