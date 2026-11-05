import Std
namespace Floor14Obstruction178
theorem fixed_loss_one_optimum (p d R : Nat)
    (hc : 9*p≤4448*d) (hw : 9*p≤3854*d+R) :
    9928285*(4200*d+p)≤42248*(1098595*d+8*p+R) := by
  have h := Nat.add_le_add (Nat.mul_le_mul_left 1023341 hc) (Nat.mul_le_mul_left 42248 hw)
  clear hc hw
  omega

theorem uniform_loss_one_optimum (p d R : Nat)
    (hc : 9*p≤4448*d) (hw : 8*p≤3356*d+R) :
    9928319*(4200*d+p)≤42248*(1098595*d+8*p+R) := by
  have h := Nat.add_le_add (Nat.mul_le_mul_left 1028039 hc) (Nat.mul_le_mul_left 42248 hw)
  clear hc hw
  omega

theorem fixed_loss_one_obstruction (p d R : Nat)
    (hc : 9*p≤4448*d) (hw : 9*p≤3854*d+R) :
    9*(227*p)+5*d≤9*(111595*d+R) := by omega

theorem uniform_loss_one_obstruction (p d R : Nat)
    (hc : 9*p≤4448*d) (hw : 8*p≤3356*d+R) :
    9*(227*p)+39*d≤9*(111595*d+R) := by omega


#print axioms fixed_loss_one_optimum
#print axioms uniform_loss_one_optimum
#print axioms fixed_loss_one_obstruction
#print axioms uniform_loss_one_obstruction
end Floor14Obstruction178
