import W232RepG1
namespace W232Rep
open WinCNF W223G1
set_option maxRecDepth 100000
theorem chk24 : G24.all (check T) = true := by decide +kernel
end W232Rep
