import Recovered129G.LocalWindowUnsat.Triple129.Data64
import Recovered129G.LocalWindowUnsat.Triple129.Data65

/-! Kernel checks of segments 253-256 of `triple129` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Triple129
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok253 : check start253 proof253 = true := by
  decide +kernel

theorem ok254 : check start254 proof254 = true := by
  decide +kernel

theorem ok255 : check start255 proof255 = true := by
  decide +kernel

theorem ok256 : andB (check start256 proof256) (cpOk (replay start256 proof256) start257) = true := by
  decide +kernel

end Snake9.LocalWindow.Triple129
