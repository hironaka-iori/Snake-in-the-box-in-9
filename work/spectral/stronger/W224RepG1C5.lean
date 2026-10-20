import W224RepG1
namespace W224Rep
open WinCNF W223G1
set_option maxRecDepth 100000
theorem chk40 : G40.all (check T) = true := by decide +kernel
theorem chk41 : G41.all (check T) = true := by decide +kernel
end W224Rep
