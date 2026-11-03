import LocalWindowUnsat.ShareWindow144.Data243
import LocalWindowUnsat.ShareWindow144.Data244

/-! Kernel checks of segments 969-972 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok969 : check start969 proof969 = true := by
  decide +kernel

theorem ok970 : check start970 proof970 = true := by
  decide +kernel

theorem ok971 : check start971 proof971 = true := by
  decide +kernel

theorem ok972 : andB (check start972 proof972) (cpOk (replay start972 proof972) start973) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
