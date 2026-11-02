import Recovered111.LocalWindowUnsat.Middle325.Data175
import Recovered111.LocalWindowUnsat.Middle325.Data176

/-! Kernel checks of segments 176-176 of `middle325` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Middle325
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok176 : andB (check start176 proof176) (cpOk (replay start176 proof176) start177) = true := by
  decide +kernel

end Snake9.LocalWindow.Middle325
