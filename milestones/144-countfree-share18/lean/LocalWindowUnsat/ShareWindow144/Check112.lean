import LocalWindowUnsat.ShareWindow144.Data112
import LocalWindowUnsat.ShareWindow144.Data113

/-! Kernel checks of segments 445-448 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok445 : check start445 proof445 = true := by
  decide +kernel

theorem ok446 : check start446 proof446 = true := by
  decide +kernel

theorem ok447 : check start447 proof447 = true := by
  decide +kernel

theorem ok448 : andB (check start448 proof448) (cpOk (replay start448 proof448) start449) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
