import Recovered129G.LocalWindowUnsat.Triple129.Data71
import Recovered129G.LocalWindowUnsat.Triple129.Data72

/-! Kernel checks of segments 281-284 of `triple129` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Triple129
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok281 : check start281 proof281 = true := by
  decide +kernel

theorem ok282 : check start282 proof282 = true := by
  decide +kernel

theorem ok283 : check start283 proof283 = true := by
  decide +kernel

theorem ok284 : andB (check start284 proof284) (cpOk (replay start284 proof284) start285) = true := by
  decide +kernel

end Snake9.LocalWindow.Triple129
