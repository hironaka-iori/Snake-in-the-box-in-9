import LocalWindowUnsat.ShareWindow144.Data149
import LocalWindowUnsat.ShareWindow144.Data150

/-! Kernel checks of segments 593-596 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok593 : check start593 proof593 = true := by
  decide +kernel

theorem ok594 : check start594 proof594 = true := by
  decide +kernel

theorem ok595 : check start595 proof595 = true := by
  decide +kernel

theorem ok596 : andB (check start596 proof596) (cpOk (replay start596 proof596) start597) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
