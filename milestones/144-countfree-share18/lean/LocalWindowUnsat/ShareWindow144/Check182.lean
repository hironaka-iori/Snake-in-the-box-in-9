import LocalWindowUnsat.ShareWindow144.Data182
import LocalWindowUnsat.ShareWindow144.Data183

/-! Kernel checks of segments 725-728 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok725 : check start725 proof725 = true := by
  decide +kernel

theorem ok726 : check start726 proof726 = true := by
  decide +kernel

theorem ok727 : check start727 proof727 = true := by
  decide +kernel

theorem ok728 : andB (check start728 proof728) (cpOk (replay start728 proof728) start729) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
