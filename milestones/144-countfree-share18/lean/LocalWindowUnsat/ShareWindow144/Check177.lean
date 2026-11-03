import LocalWindowUnsat.ShareWindow144.Data177
import LocalWindowUnsat.ShareWindow144.Data178

/-! Kernel checks of segments 705-708 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok705 : check start705 proof705 = true := by
  decide +kernel

theorem ok706 : check start706 proof706 = true := by
  decide +kernel

theorem ok707 : check start707 proof707 = true := by
  decide +kernel

theorem ok708 : andB (check start708 proof708) (cpOk (replay start708 proof708) start709) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
