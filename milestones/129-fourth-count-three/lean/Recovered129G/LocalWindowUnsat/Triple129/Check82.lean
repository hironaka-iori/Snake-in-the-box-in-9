import Recovered129G.LocalWindowUnsat.Triple129.Data82
import Recovered129G.LocalWindowUnsat.Triple129.Data83

/-! Kernel checks of segments 325-328 of `triple129` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Triple129
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok325 : check start325 proof325 = true := by
  decide +kernel

theorem ok326 : check start326 proof326 = true := by
  decide +kernel

theorem ok327 : check start327 proof327 = true := by
  decide +kernel

theorem ok328 : andB (check start328 proof328) (cpOk (replay start328 proof328) start329) = true := by
  decide +kernel

end Snake9.LocalWindow.Triple129
