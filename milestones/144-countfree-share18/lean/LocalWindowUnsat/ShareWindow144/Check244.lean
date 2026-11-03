import LocalWindowUnsat.ShareWindow144.Data244
import LocalWindowUnsat.ShareWindow144.Data245

/-! Kernel checks of segments 973-976 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok973 : check start973 proof973 = true := by
  decide +kernel

theorem ok974 : check start974 proof974 = true := by
  decide +kernel

theorem ok975 : check start975 proof975 = true := by
  decide +kernel

theorem ok976 : andB (check start976 proof976) (cpOk (replay start976 proof976) start977) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
