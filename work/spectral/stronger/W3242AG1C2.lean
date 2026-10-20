import W3242AG1
namespace W3242A
open WinCNF W223G1
set_option maxRecDepth 100000
theorem chk16 : G16.all (check T) = true := by decide +kernel
theorem chk17 : G17.all (check T) = true := by decide +kernel
theorem chk18 : G18.all (check T) = true := by decide +kernel
end W3242A
