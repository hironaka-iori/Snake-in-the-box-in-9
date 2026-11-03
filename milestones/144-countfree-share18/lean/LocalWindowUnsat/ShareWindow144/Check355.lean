import LocalWindowUnsat.ShareWindow144.Data355
import LocalWindowUnsat.ShareWindow144.Data356

/-! Kernel checks of segments 1417-1420 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1417 : check start1417 proof1417 = true := by
  decide +kernel

theorem ok1418 : check start1418 proof1418 = true := by
  decide +kernel

theorem ok1419 : check start1419 proof1419 = true := by
  decide +kernel

theorem ok1420 : andB (check start1420 proof1420) (cpOk (replay start1420 proof1420) start1421) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
