import Recovered129G.LocalWindowUnsat.Triple129.Data65
import Recovered129G.LocalWindowUnsat.Triple129.Data66

/-! Kernel checks of segments 257-260 of `triple129` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Triple129
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok257 : check start257 proof257 = true := by
  decide +kernel

theorem ok258 : check start258 proof258 = true := by
  decide +kernel

theorem ok259 : check start259 proof259 = true := by
  decide +kernel

theorem ok260 : andB (check start260 proof260) (cpOk (replay start260 proof260) start261) = true := by
  decide +kernel

end Snake9.LocalWindow.Triple129
