import LocalWindowUnsat.ShareWindow144.Data600
import LocalWindowUnsat.ShareWindow144.Data601

/-! Kernel checks of segments 2397-2400 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok2397 : check start2397 proof2397 = true := by
  decide +kernel

theorem ok2398 : check start2398 proof2398 = true := by
  decide +kernel

theorem ok2399 : check start2399 proof2399 = true := by
  decide +kernel

theorem ok2400 : andB (check start2400 proof2400) (cpOk (replay start2400 proof2400) start2401) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
