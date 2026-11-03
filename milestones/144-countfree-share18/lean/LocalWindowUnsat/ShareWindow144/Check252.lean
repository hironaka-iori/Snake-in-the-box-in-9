import LocalWindowUnsat.ShareWindow144.Data252
import LocalWindowUnsat.ShareWindow144.Data253

/-! Kernel checks of segments 1005-1008 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1005 : check start1005 proof1005 = true := by
  decide +kernel

theorem ok1006 : check start1006 proof1006 = true := by
  decide +kernel

theorem ok1007 : check start1007 proof1007 = true := by
  decide +kernel

theorem ok1008 : andB (check start1008 proof1008) (cpOk (replay start1008 proof1008) start1009) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
