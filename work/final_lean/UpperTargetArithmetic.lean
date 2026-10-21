import Std

/-! Independent integer checks only. None of the hypotheses below is asserted
to hold for arbitrary snakes by this module. -/
namespace Snake9.UpperTargetArithmetic

theorem packing231 (v G : Nat) (hup : G + 840*v ≤ 221136)
    (hlo : 114*v ≤ G + 1145) : v ≤ 232 := by omega

theorem packing230 (v G : Nat) (hup : G + 840*v ≤ 221136)
    (hlo : 114*v ≤ G + 191) : v ≤ 231 := by omega

theorem six_centres231 (m A S : Nat) (hm : 7 ≤ m)
    (hwalk : 9*m ≤ 2*A+59) (hshare : 21*(m-7) ≤ 6*S)
    (hinc : 21*(A+8)+S+735*(m+1) ≤ 193494) : m ≤ 231 := by omega

/-- The seven-centre lead needs C ≤ 703, or D ≤ 10 in C = 693 + D.
This proves the arithmetic threshold, not the potential or its boundary. -/
theorem seven_centres230 (m A S C : Nat) (hm : 8 ≤ m) (hc : C ≤ 703)
    (hwalk : 89*m ≤ 19*A+C) (hshare : 27*(m-8) ≤ 7*S)
    (hinc : 21*(A+8)+S+735*(m+1) ≤ 193494) : m ≤ 230 := by omega

#print axioms packing231
#print axioms packing230
#print axioms six_centres231
#print axioms seven_centres230
end Snake9.UpperTargetArithmetic
