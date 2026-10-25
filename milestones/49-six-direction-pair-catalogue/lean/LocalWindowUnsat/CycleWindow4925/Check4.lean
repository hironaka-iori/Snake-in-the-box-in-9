import LocalWindowUnsat.CycleWindow4925.Data18
import LocalWindowUnsat.CycleWindow4925.Data19
import LocalWindowUnsat.CycleWindow4925.Data20
import LocalWindowUnsat.CycleWindow4925.Data21
import LocalWindowUnsat.CycleWindow4925.Data22

/-! Kernel checks of segments 19-22 of `cycle4925` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.CycleWindow4925
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok19 : check start19 proof19 = true := by
  decide +kernel

theorem ok20 : andB (check start20 proof20) (cpOk (replay start20 proof20) start21) = true := by
  decide +kernel

theorem ok21 : check start21 proof21 = true := by
  decide +kernel

theorem ok22 : andB (check start22 proof22) (hasEmpty (replay start22 proof22) 2048) = true := by
  decide +kernel

end Snake9.LocalWindow.CycleWindow4925
