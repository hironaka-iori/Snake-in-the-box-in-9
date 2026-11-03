import LocalWindowUnsat.ShareWindow144.Data524
import LocalWindowUnsat.ShareWindow144.Data525

/-! Kernel checks of segments 2093-2096 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok2093 : check start2093 proof2093 = true := by
  decide +kernel

theorem ok2094 : check start2094 proof2094 = true := by
  decide +kernel

theorem ok2095 : check start2095 proof2095 = true := by
  decide +kernel

theorem ok2096 : andB (check start2096 proof2096) (cpOk (replay start2096 proof2096) start2097) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
