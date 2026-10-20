import W323DisG1
namespace W323Dis
open WinCNF W223G1
set_option maxRecDepth 100000
theorem chk48 : G48.all (check T) = true := by decide +kernel
theorem chk49 : G49.all (check T) = true := by decide +kernel
theorem chk50 : G50.all (check T) = true := by decide +kernel
theorem chk51 : G51.all (check T) = true := by decide +kernel
theorem chk52 : G52.all (check T) = true := by decide +kernel
theorem chk53 : G53.all (check T) = true := by decide +kernel
theorem chk54 : G54.all (check T) = true := by decide +kernel
theorem chk55 : G55.all (check T) = true := by decide +kernel
end W323Dis
