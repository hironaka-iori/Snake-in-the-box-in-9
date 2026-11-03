import Recovered129G.LocalWindowUnsat.Triple129.Data54
import Recovered129G.LocalWindowUnsat.Triple129.Data55

/-! Kernel checks of segments 213-216 of `triple129` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Triple129
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok213 : check start213 proof213 = true := by
  decide +kernel

theorem ok214 : check start214 proof214 = true := by
  decide +kernel

theorem ok215 : check start215 proof215 = true := by
  decide +kernel

theorem ok216 : andB (check start216 proof216) (cpOk (replay start216 proof216) start217) = true := by
  decide +kernel

end Snake9.LocalWindow.Triple129
