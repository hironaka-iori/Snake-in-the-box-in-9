import W223G1Data
import W223DisInputs
/-! Kernel check: every used clause of `W223Dis.F` passes the G1 clause checker. -/
namespace W223G1
set_option maxRecDepth 100000
theorem blocksOK_dis : blocksOK tabDis = true := by decide +kernel
theorem check_dis : W223Dis.F.all (check tabDis) = true := by decide +kernel
end W223G1
