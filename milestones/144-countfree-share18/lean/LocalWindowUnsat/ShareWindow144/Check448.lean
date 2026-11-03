import LocalWindowUnsat.ShareWindow144.Data448
import LocalWindowUnsat.ShareWindow144.Data449

/-! Kernel checks of segments 1789-1792 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1789 : check start1789 proof1789 = true := by
  decide +kernel

theorem ok1790 : check start1790 proof1790 = true := by
  decide +kernel

theorem ok1791 : check start1791 proof1791 = true := by
  decide +kernel

theorem ok1792 : andB (check start1792 proof1792) (cpOk (replay start1792 proof1792) start1793) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
