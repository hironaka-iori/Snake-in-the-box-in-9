import W224RepG1
namespace W224Rep
open WinCNF W223G1
set_option maxRecDepth 100000
theorem chk0 : G0.all (check T) = true := by decide +kernel
theorem chk1 : G1.all (check T) = true := by decide +kernel
theorem chk2 : G2.all (check T) = true := by decide +kernel
theorem chk3 : G3.all (check T) = true := by decide +kernel
theorem chk4 : G4.all (check T) = true := by decide +kernel
theorem chk5 : G5.all (check T) = true := by decide +kernel
theorem chk6 : G6.all (check T) = true := by decide +kernel
theorem chk7 : G7.all (check T) = true := by decide +kernel
end W224Rep
