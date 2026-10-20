import W323DisG1
namespace W323Dis
open WinCNF W223G1
set_option maxRecDepth 100000
theorem chk24 : G24.all (check T) = true := by decide +kernel
theorem chk25 : G25.all (check T) = true := by decide +kernel
theorem chk26 : G26.all (check T) = true := by decide +kernel
theorem chk27 : G27.all (check T) = true := by decide +kernel
theorem chk28 : G28.all (check T) = true := by decide +kernel
theorem chk29 : G29.all (check T) = true := by decide +kernel
theorem chk30 : G30.all (check T) = true := by decide +kernel
theorem chk31 : G31.all (check T) = true := by decide +kernel
end W323Dis
