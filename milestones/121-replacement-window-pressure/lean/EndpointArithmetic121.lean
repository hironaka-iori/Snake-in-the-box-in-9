import ReferenceInterface

namespace Snake9.EndpointArithmetic121

theorem conditional_charge_bound (m W p d R C t : Int)
    (hd : 0 ≤ d) (hC : 0 ≤ C) (ht : t ≤ 14)
    (hbudget : W + 4200*m ≤ 1098960)
    (hpotential : p*(m-8)-R ≤ d*(W+C*t)) :
    (4200*d+p)*m ≤ 1098960*d+14*C*d+8*p+R := by
  have h1 := mul_le_mul_of_nonneg_left hbudget hd
  have h2 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ht hC) hd
  nlinarith

#print axioms conditional_charge_bound
end Snake9.EndpointArithmetic121
