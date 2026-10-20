import W232DisG1
namespace W232Dis
open WinCNF W223G1
set_option maxRecDepth 100000
theorem chk48 : G48.all (check T) = true := by decide +kernel
theorem chk49 : G49.all (check T) = true := by decide +kernel
end W232Dis
