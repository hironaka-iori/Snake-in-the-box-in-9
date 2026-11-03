import LocalWindowUnsat.ShareWindow144.Data188
import LocalWindowUnsat.ShareWindow144.Data189

/-! Kernel checks of segments 749-752 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok749 : check start749 proof749 = true := by
  decide +kernel

theorem ok750 : check start750 proof750 = true := by
  decide +kernel

theorem ok751 : check start751 proof751 = true := by
  decide +kernel

theorem ok752 : andB (check start752 proof752) (cpOk (replay start752 proof752) start753) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
