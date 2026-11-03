import LocalWindowUnsat.ShareWindow144.Data176
import LocalWindowUnsat.ShareWindow144.Data177

/-! Kernel checks of segments 701-704 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok701 : check start701 proof701 = true := by
  decide +kernel

theorem ok702 : check start702 proof702 = true := by
  decide +kernel

theorem ok703 : check start703 proof703 = true := by
  decide +kernel

theorem ok704 : andB (check start704 proof704) (cpOk (replay start704 proof704) start705) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
