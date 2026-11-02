import Recovered107.LocalWindowUnsat.Q012A11.Data0
import Recovered107.LocalWindowUnsat.Q012A11.Data1

/-! Kernel checks of segments 1-1 of `d012_a1_1` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Q012A11
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok1 : check start1 proof1 = true := by
  decide +kernel

end Snake9.LocalWindow.Q012A11
