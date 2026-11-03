import Recovered129G.LocalWindowUnsat.Triple129.Data88
import Recovered129G.LocalWindowUnsat.Triple129.Data89

/-! Kernel checks of segments 349-352 of `triple129` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Triple129
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok349 : check start349 proof349 = true := by
  decide +kernel

theorem ok350 : check start350 proof350 = true := by
  decide +kernel

theorem ok351 : check start351 proof351 = true := by
  decide +kernel

theorem ok352 : andB (check start352 proof352) (cpOk (replay start352 proof352) start353) = true := by
  decide +kernel

end Snake9.LocalWindow.Triple129
