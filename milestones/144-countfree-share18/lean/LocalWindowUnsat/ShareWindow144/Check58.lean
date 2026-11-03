import LocalWindowUnsat.ShareWindow144.Data58
import LocalWindowUnsat.ShareWindow144.Data59

/-! Kernel checks of segments 229-232 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok229 : check start229 proof229 = true := by
  decide +kernel

theorem ok230 : check start230 proof230 = true := by
  decide +kernel

theorem ok231 : check start231 proof231 = true := by
  decide +kernel

theorem ok232 : andB (check start232 proof232) (cpOk (replay start232 proof232) start233) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
