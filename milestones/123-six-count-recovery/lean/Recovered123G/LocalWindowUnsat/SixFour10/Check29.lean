import Recovered123G.LocalWindowUnsat.SixFour10.Data29
import Recovered123G.LocalWindowUnsat.SixFour10.Data30

/-! Kernel checks of segments 169-174 of `four10` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.SixFour10
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok169 : check start169 proof169 = true := by
  decide +kernel

theorem ok170 : check start170 proof170 = true := by
  decide +kernel

theorem ok171 : check start171 proof171 = true := by
  decide +kernel

theorem ok172 : check start172 proof172 = true := by
  decide +kernel

theorem ok173 : check start173 proof173 = true := by
  decide +kernel

theorem ok174 : andB (check start174 proof174) (cpOk (replay start174 proof174) start175) = true := by
  decide +kernel

end Snake9.LocalWindow.SixFour10
