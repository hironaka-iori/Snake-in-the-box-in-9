import LocalWindowUnsat.ShareWindow144.Data383
import LocalWindowUnsat.ShareWindow144.Data384

/-! Kernel checks of segments 1529-1532 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1529 : check start1529 proof1529 = true := by
  decide +kernel

theorem ok1530 : check start1530 proof1530 = true := by
  decide +kernel

theorem ok1531 : check start1531 proof1531 = true := by
  decide +kernel

theorem ok1532 : andB (check start1532 proof1532) (cpOk (replay start1532 proof1532) start1533) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
