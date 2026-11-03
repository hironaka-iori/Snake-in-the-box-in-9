import Recovered129G.LocalWindowUnsat.Triple129.Data77
import Recovered129G.LocalWindowUnsat.Triple129.Data78

/-! Kernel checks of segments 305-308 of `triple129` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Triple129
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok305 : check start305 proof305 = true := by
  decide +kernel

theorem ok306 : check start306 proof306 = true := by
  decide +kernel

theorem ok307 : check start307 proof307 = true := by
  decide +kernel

theorem ok308 : andB (check start308 proof308) (cpOk (replay start308 proof308) start309) = true := by
  decide +kernel

end Snake9.LocalWindow.Triple129
