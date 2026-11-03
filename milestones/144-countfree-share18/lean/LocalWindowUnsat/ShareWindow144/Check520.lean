import LocalWindowUnsat.ShareWindow144.Data520
import LocalWindowUnsat.ShareWindow144.Data521

/-! Kernel checks of segments 2077-2080 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok2077 : check start2077 proof2077 = true := by
  decide +kernel

theorem ok2078 : check start2078 proof2078 = true := by
  decide +kernel

theorem ok2079 : check start2079 proof2079 = true := by
  decide +kernel

theorem ok2080 : andB (check start2080 proof2080) (cpOk (replay start2080 proof2080) start2081) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
