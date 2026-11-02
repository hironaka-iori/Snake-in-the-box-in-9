import LocalWindowUnsat.Middle325.Data191
import LocalWindowUnsat.Middle325.Data192

/-! Kernel checks of segments 192-192 of `middle325` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Middle325
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok192 : andB (check start192 proof192) (cpOk (replay start192 proof192) start193) = true := by
  decide +kernel

end Snake9.LocalWindow.Middle325
