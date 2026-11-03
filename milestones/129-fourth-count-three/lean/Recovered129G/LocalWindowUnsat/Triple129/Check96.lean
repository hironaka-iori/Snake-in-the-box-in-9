import Recovered129G.LocalWindowUnsat.Triple129.Data96
import Recovered129G.LocalWindowUnsat.Triple129.Data97

/-! Kernel checks of segments 381-384 of `triple129` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Triple129
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok381 : check start381 proof381 = true := by
  decide +kernel

theorem ok382 : check start382 proof382 = true := by
  decide +kernel

theorem ok383 : check start383 proof383 = true := by
  decide +kernel

theorem ok384 : andB (check start384 proof384) (cpOk (replay start384 proof384) start385) = true := by
  decide +kernel

end Snake9.LocalWindow.Triple129
