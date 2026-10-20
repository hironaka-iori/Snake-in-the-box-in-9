import W323DisG1
namespace W323Dis
open WinCNF W223G1
set_option maxRecDepth 100000
theorem chk40 : G40.all (check T) = true := by decide +kernel
theorem chk41 : G41.all (check T) = true := by decide +kernel
theorem chk42 : G42.all (check T) = true := by decide +kernel
theorem chk43 : G43.all (check T) = true := by decide +kernel
theorem chk44 : G44.all (check T) = true := by decide +kernel
theorem chk45 : G45.all (check T) = true := by decide +kernel
theorem chk46 : G46.all (check T) = true := by decide +kernel
theorem chk47 : G47.all (check T) = true := by decide +kernel
end W323Dis
