import W41cRepG1
namespace W41cRep
open WinCNF W223G1
set_option maxRecDepth 100000
theorem chk0 : G0.all (check T) = true := by decide +kernel
theorem chk1 : G1.all (check T) = true := by decide +kernel
theorem chk2 : G2.all (check T) = true := by decide +kernel
theorem chk3 : G3.all (check T) = true := by decide +kernel
theorem chk4 : G4.all (check T) = true := by decide +kernel
theorem chk5 : G5.all (check T) = true := by decide +kernel
end W41cRep
