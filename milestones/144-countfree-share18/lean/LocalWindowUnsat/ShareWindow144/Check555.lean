import LocalWindowUnsat.ShareWindow144.Data555
import LocalWindowUnsat.ShareWindow144.Data556

/-! Kernel checks of segments 2217-2220 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok2217 : check start2217 proof2217 = true := by
  decide +kernel

theorem ok2218 : check start2218 proof2218 = true := by
  decide +kernel

theorem ok2219 : check start2219 proof2219 = true := by
  decide +kernel

theorem ok2220 : andB (check start2220 proof2220) (cpOk (replay start2220 proof2220) start2221) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
