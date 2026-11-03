import Recovered129G.LocalWindowUnsat.Triple129.Data21
import Recovered129G.LocalWindowUnsat.Triple129.Data22

/-! Kernel checks of segments 81-84 of `triple129` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Triple129
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok81 : check start81 proof81 = true := by
  decide +kernel

theorem ok82 : check start82 proof82 = true := by
  decide +kernel

theorem ok83 : check start83 proof83 = true := by
  decide +kernel

theorem ok84 : andB (check start84 proof84) (cpOk (replay start84 proof84) start85) = true := by
  decide +kernel

end Snake9.LocalWindow.Triple129
