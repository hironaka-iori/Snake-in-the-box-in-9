import LocalWindowUnsat.ShareWindow144.Data151
import LocalWindowUnsat.ShareWindow144.Data152

/-! Kernel checks of segments 601-604 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok601 : check start601 proof601 = true := by
  decide +kernel

theorem ok602 : check start602 proof602 = true := by
  decide +kernel

theorem ok603 : check start603 proof603 = true := by
  decide +kernel

theorem ok604 : andB (check start604 proof604) (cpOk (replay start604 proof604) start605) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
