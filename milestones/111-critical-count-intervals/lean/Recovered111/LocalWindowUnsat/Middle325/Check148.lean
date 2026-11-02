import Recovered111.LocalWindowUnsat.Middle325.Data147
import Recovered111.LocalWindowUnsat.Middle325.Data148

/-! Kernel checks of segments 148-148 of `middle325` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Middle325
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok148 : andB (check start148 proof148) (cpOk (replay start148 proof148) start149) = true := by
  decide +kernel

end Snake9.LocalWindow.Middle325
