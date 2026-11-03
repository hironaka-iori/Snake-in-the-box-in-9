import LocalWindowUnsat.ShareWindow144.Data55
import LocalWindowUnsat.ShareWindow144.Data56

/-! Kernel checks of segments 217-220 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok217 : check start217 proof217 = true := by
  decide +kernel

theorem ok218 : check start218 proof218 = true := by
  decide +kernel

theorem ok219 : check start219 proof219 = true := by
  decide +kernel

theorem ok220 : andB (check start220 proof220) (cpOk (replay start220 proof220) start221) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
