import Recovered129G.LocalWindowUnsat.Triple129.Data90
import Recovered129G.LocalWindowUnsat.Triple129.Data91

/-! Kernel checks of segments 357-360 of `triple129` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Triple129
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok357 : check start357 proof357 = true := by
  decide +kernel

theorem ok358 : check start358 proof358 = true := by
  decide +kernel

theorem ok359 : check start359 proof359 = true := by
  decide +kernel

theorem ok360 : andB (check start360 proof360) (cpOk (replay start360 proof360) start361) = true := by
  decide +kernel

end Snake9.LocalWindow.Triple129
