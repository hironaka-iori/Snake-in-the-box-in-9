import W2423AG1
namespace W2423A
open WinCNF W223G1
set_option maxRecDepth 100000
theorem chk24 : G24.all (check T) = true := by decide +kernel
theorem chk25 : G25.all (check T) = true := by decide +kernel
theorem chk26 : G26.all (check T) = true := by decide +kernel
end W2423A
