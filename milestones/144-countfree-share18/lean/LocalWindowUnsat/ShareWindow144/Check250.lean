import LocalWindowUnsat.ShareWindow144.Data250
import LocalWindowUnsat.ShareWindow144.Data251

/-! Kernel checks of segments 997-1000 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok997 : check start997 proof997 = true := by
  decide +kernel

theorem ok998 : check start998 proof998 = true := by
  decide +kernel

theorem ok999 : check start999 proof999 = true := by
  decide +kernel

theorem ok1000 : andB (check start1000 proof1000) (cpOk (replay start1000 proof1000) start1001) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
