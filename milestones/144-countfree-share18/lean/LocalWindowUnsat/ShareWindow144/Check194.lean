import LocalWindowUnsat.ShareWindow144.Data194
import LocalWindowUnsat.ShareWindow144.Data195

/-! Kernel checks of segments 773-776 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok773 : check start773 proof773 = true := by
  decide +kernel

theorem ok774 : check start774 proof774 = true := by
  decide +kernel

theorem ok775 : check start775 proof775 = true := by
  decide +kernel

theorem ok776 : andB (check start776 proof776) (cpOk (replay start776 proof776) start777) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
