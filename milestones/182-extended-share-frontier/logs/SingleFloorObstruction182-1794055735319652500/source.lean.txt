import Std
namespace SingleFloorObstruction182

theorem loss_one_comparison_floor (p d R : Nat)
    (hc : 9*p≤4448*d) (hw : 8*p≤3358*d+R) :
    9928301*(4200*d+p)≤42248*(1098595*d+8*p+R) := by
  have h := Nat.add_le_add (Nat.mul_le_mul_left 1028037 hc)
    (Nat.mul_le_mul_left 42248 hw)
  clear hc hw
  omega

theorem loss_one_strict_obstruction (p d R : Nat) (hd : 0<d)
    (hc : 9*p≤4448*d) (hw : 8*p≤3358*d+R) :
    235*(4200*d+p)<1098595*d+8*p+R := by
  have h := loss_one_comparison_floor p d R hc hw
  omega

theorem lower_comparison_value :
    (9928301 : Nat)=235*42248+21 ∧
    9928301*(4200*9+4448)=42248*(1098595*9+8*4448+5362) := by decide

#print axioms loss_one_comparison_floor
#print axioms loss_one_strict_obstruction
#print axioms lower_comparison_value
end SingleFloorObstruction182
