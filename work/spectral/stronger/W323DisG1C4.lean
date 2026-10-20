import W323DisG1
namespace W323Dis
open WinCNF W223G1
set_option maxRecDepth 100000
theorem chk32 : G32.all (check T) = true := by decide +kernel
theorem chk33 : G33.all (check T) = true := by decide +kernel
theorem chk34 : G34.all (check T) = true := by decide +kernel
theorem chk35 : G35.all (check T) = true := by decide +kernel
theorem chk36 : G36.all (check T) = true := by decide +kernel
theorem chk37 : G37.all (check T) = true := by decide +kernel
theorem chk38 : G38.all (check T) = true := by decide +kernel
theorem chk39 : G39.all (check T) = true := by decide +kernel
end W323Dis
