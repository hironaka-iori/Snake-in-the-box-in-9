import LocalWindowUnsat.ShareWindow144.Data54
import LocalWindowUnsat.ShareWindow144.Data55

/-! Kernel checks of segments 213-216 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok213 : check start213 proof213 = true := by
  decide +kernel

theorem ok214 : check start214 proof214 = true := by
  decide +kernel

theorem ok215 : check start215 proof215 = true := by
  decide +kernel

theorem ok216 : andB (check start216 proof216) (cpOk (replay start216 proof216) start217) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
