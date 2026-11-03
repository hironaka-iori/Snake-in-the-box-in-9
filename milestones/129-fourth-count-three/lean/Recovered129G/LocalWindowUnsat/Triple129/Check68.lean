import Recovered129G.LocalWindowUnsat.Triple129.Data68
import Recovered129G.LocalWindowUnsat.Triple129.Data69

/-! Kernel checks of segments 269-272 of `triple129` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Triple129
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok269 : check start269 proof269 = true := by
  decide +kernel

theorem ok270 : check start270 proof270 = true := by
  decide +kernel

theorem ok271 : check start271 proof271 = true := by
  decide +kernel

theorem ok272 : andB (check start272 proof272) (cpOk (replay start272 proof272) start273) = true := by
  decide +kernel

end Snake9.LocalWindow.Triple129
