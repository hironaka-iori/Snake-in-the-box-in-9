import Recovered111.LocalWindowUnsat.Middle325.Data7
import Recovered111.LocalWindowUnsat.Middle325.Data8

/-! Kernel checks of segments 8-8 of `middle325` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Middle325
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok8 : andB (check start8 proof8) (cpOk (replay start8 proof8) start9) = true := by
  decide +kernel

end Snake9.LocalWindow.Middle325
