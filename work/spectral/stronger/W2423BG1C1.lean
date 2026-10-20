import W2423BG1
namespace W2423B
open WinCNF W223G1
set_option maxRecDepth 100000
theorem chk8 : G8.all (check T) = true := by decide +kernel
theorem chk9 : G9.all (check T) = true := by decide +kernel
theorem chk10 : G10.all (check T) = true := by decide +kernel
theorem chk11 : G11.all (check T) = true := by decide +kernel
theorem chk12 : G12.all (check T) = true := by decide +kernel
theorem chk13 : G13.all (check T) = true := by decide +kernel
theorem chk14 : G14.all (check T) = true := by decide +kernel
theorem chk15 : G15.all (check T) = true := by decide +kernel
end W2423B
