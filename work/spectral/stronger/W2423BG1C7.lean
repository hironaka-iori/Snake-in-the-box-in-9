import W2423BG1
namespace W2423B
open WinCNF W223G1
set_option maxRecDepth 100000
theorem chk56 : G56.all (check T) = true := by decide +kernel
theorem chk57 : G57.all (check T) = true := by decide +kernel
end W2423B
