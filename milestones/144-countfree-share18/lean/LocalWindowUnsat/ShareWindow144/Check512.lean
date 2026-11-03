import LocalWindowUnsat.ShareWindow144.Data512
import LocalWindowUnsat.ShareWindow144.Data513

/-! Kernel checks of segments 2045-2048 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok2045 : check start2045 proof2045 = true := by
  decide +kernel

theorem ok2046 : check start2046 proof2046 = true := by
  decide +kernel

theorem ok2047 : check start2047 proof2047 = true := by
  decide +kernel

theorem ok2048 : andB (check start2048 proof2048) (cpOk (replay start2048 proof2048) start2049) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
