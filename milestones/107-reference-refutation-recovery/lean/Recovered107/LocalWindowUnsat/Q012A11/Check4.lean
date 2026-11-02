import Recovered107.LocalWindowUnsat.Q012A11.Data3
import Recovered107.LocalWindowUnsat.Q012A11.Data4

/-! Kernel checks of segments 4-4 of `d012_a1_1` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Q012A11
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok4 : andB (check start4 proof4) (cpOk (replay start4 proof4) start5) = true := by
  decide +kernel

end Snake9.LocalWindow.Q012A11
