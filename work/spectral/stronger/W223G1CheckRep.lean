import W223G1Data
import W223RepInputs
/-! Kernel check: every used clause of `W223Rep.F` passes the G1 clause checker. -/
namespace W223G1
set_option maxRecDepth 100000
theorem blocksOK_rep : blocksOK tabRep = true := by decide +kernel
theorem check_rep : W223Rep.F.all (check tabRep) = true := by decide +kernel
end W223G1
