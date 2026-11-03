import LocalWindowUnsat.ShareWindow144.Data602
import LocalWindowUnsat.ShareWindow144.Data603

/-! Kernel checks of segments 2405-2408 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok2405 : check start2405 proof2405 = true := by
  decide +kernel

theorem ok2406 : check start2406 proof2406 = true := by
  decide +kernel

theorem ok2407 : check start2407 proof2407 = true := by
  decide +kernel

theorem ok2408 : andB (check start2408 proof2408) (cpOk (replay start2408 proof2408) start2409) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
