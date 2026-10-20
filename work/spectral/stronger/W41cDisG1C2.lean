import W41cDisG1
namespace W41cDis
open WinCNF W223G1
set_option maxRecDepth 100000
theorem chk16 : G16.all (check T) = true := by decide +kernel
theorem chk17 : G17.all (check T) = true := by decide +kernel
theorem chk18 : G18.all (check T) = true := by decide +kernel
theorem chk19 : G19.all (check T) = true := by decide +kernel
theorem chk20 : G20.all (check T) = true := by decide +kernel
end W41cDis
