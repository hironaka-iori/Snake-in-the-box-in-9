import W323RepG1
namespace W323Rep
open WinCNF W223G1
set_option maxRecDepth 100000
theorem chk16 : G16.all (check T) = true := by decide +kernel
theorem chk17 : G17.all (check T) = true := by decide +kernel
theorem chk18 : G18.all (check T) = true := by decide +kernel
theorem chk19 : G19.all (check T) = true := by decide +kernel
theorem chk20 : G20.all (check T) = true := by decide +kernel
theorem chk21 : G21.all (check T) = true := by decide +kernel
theorem chk22 : G22.all (check T) = true := by decide +kernel
theorem chk23 : G23.all (check T) = true := by decide +kernel
end W323Rep
