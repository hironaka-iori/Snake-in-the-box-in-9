import LocalWindowUnsat.ShareWindow144.Data137
import LocalWindowUnsat.ShareWindow144.Data138

/-! Kernel checks of segments 545-548 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok545 : check start545 proof545 = true := by
  decide +kernel

theorem ok546 : check start546 proof546 = true := by
  decide +kernel

theorem ok547 : check start547 proof547 = true := by
  decide +kernel

theorem ok548 : andB (check start548 proof548) (cpOk (replay start548 proof548) start549) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
