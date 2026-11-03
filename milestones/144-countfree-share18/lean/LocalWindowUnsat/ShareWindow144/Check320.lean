import LocalWindowUnsat.ShareWindow144.Data320
import LocalWindowUnsat.ShareWindow144.Data321

/-! Kernel checks of segments 1277-1280 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1277 : check start1277 proof1277 = true := by
  decide +kernel

theorem ok1278 : check start1278 proof1278 = true := by
  decide +kernel

theorem ok1279 : check start1279 proof1279 = true := by
  decide +kernel

theorem ok1280 : andB (check start1280 proof1280) (cpOk (replay start1280 proof1280) start1281) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
