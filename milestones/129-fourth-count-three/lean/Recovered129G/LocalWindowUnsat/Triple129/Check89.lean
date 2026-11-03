import Recovered129G.LocalWindowUnsat.Triple129.Data89
import Recovered129G.LocalWindowUnsat.Triple129.Data90

/-! Kernel checks of segments 353-356 of `triple129` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Triple129
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok353 : check start353 proof353 = true := by
  decide +kernel

theorem ok354 : check start354 proof354 = true := by
  decide +kernel

theorem ok355 : check start355 proof355 = true := by
  decide +kernel

theorem ok356 : andB (check start356 proof356) (cpOk (replay start356 proof356) start357) = true := by
  decide +kernel

end Snake9.LocalWindow.Triple129
