import LocalWindowUnsat.Middle325.Data187
import LocalWindowUnsat.Middle325.Data188

/-! Kernel checks of segments 188-188 of `middle325` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Middle325
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok188 : andB (check start188 proof188) (cpOk (replay start188 proof188) start189) = true := by
  decide +kernel

end Snake9.LocalWindow.Middle325
