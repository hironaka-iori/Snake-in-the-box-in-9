import W323DisG1
namespace W323Dis
open WinCNF W223G1
set_option maxRecDepth 100000
theorem chk56 : G56.all (check T) = true := by decide +kernel
theorem chk57 : G57.all (check T) = true := by decide +kernel
theorem chk58 : G58.all (check T) = true := by decide +kernel
theorem chk59 : G59.all (check T) = true := by decide +kernel
end W323Dis
