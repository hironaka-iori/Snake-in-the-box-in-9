import LocalWindowUnsat.ShareWindow144.Data599
import LocalWindowUnsat.ShareWindow144.Data600

/-! Kernel checks of segments 2393-2396 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok2393 : check start2393 proof2393 = true := by
  decide +kernel

theorem ok2394 : check start2394 proof2394 = true := by
  decide +kernel

theorem ok2395 : check start2395 proof2395 = true := by
  decide +kernel

theorem ok2396 : andB (check start2396 proof2396) (cpOk (replay start2396 proof2396) start2397) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
