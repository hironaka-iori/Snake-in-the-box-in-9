import LocalWindowUnsat.Middle325.Data5
import LocalWindowUnsat.Middle325.Data6

/-! Kernel checks of segments 6-6 of `middle325` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Middle325
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok6 : andB (check start6 proof6) (cpOk (replay start6 proof6) start7) = true := by
  decide +kernel

end Snake9.LocalWindow.Middle325
