import Std
namespace SingleCritical184

theorem comparison (m W G L : Nat) (hm : 8≤m)
    (hb : G+840*(m+1)+L≤221136) (hp : W+2880≤5*G)
    (hw : 4454*(m-8)≤9*W+5421) :
    42254*m+45*L≤9928453 := by omega

theorem upper234 (m W G L : Nat) (hm : 8≤m)
    (hb : G+840*(m+1)+L≤221136) (hp : W+2880≤5*G)
    (hw : 4454*(m-8)≤9*W+5421) : m≤234 := by
  have := comparison m W G L hm hb hp hw
  omega

theorem comparison_optimum (p d R : Nat)
    (hc : 9*p≤4454*d) (hw : 24*p≤11275*d+R) :
    9928453*(4200*d+p)≤42254*(1098600*d+8*p+R) := by
  have h := Nat.add_le_add (Nat.mul_le_mul_left 952925 hc)
    (Nat.mul_le_mul_left 42254 hw)
  clear hc hw
  omega

theorem optimum_value :
    (9928453 : Nat)+1237=235*42254 ∧
    9928453*(4200*9+4454)=42254*(1098600*9+8*4454+5421) := by decide

theorem floor14_zero_loss_obstruction (p d R : Nat) (hd : 0<d)
    (hc : 9*p≤4448*d) (hw : 8*p≤3356*d+R) :
    235*(4200*d+p)<1098600*d+8*p+R := by omega

#print axioms comparison
#print axioms upper234
#print axioms comparison_optimum
#print axioms optimum_value
#print axioms floor14_zero_loss_obstruction
end SingleCritical184
