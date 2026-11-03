import LocalWindowUnsat.ShareWindow144.Data88
import LocalWindowUnsat.ShareWindow144.Data89

/-! Kernel checks of segments 349-352 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok349 : check start349 proof349 = true := by
  decide +kernel

theorem ok350 : check start350 proof350 = true := by
  decide +kernel

theorem ok351 : check start351 proof351 = true := by
  decide +kernel

theorem ok352 : andB (check start352 proof352) (cpOk (replay start352 proof352) start353) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
