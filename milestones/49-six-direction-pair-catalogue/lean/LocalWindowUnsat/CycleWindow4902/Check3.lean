import LocalWindowUnsat.CycleWindow4902.Data12
import LocalWindowUnsat.CycleWindow4902.Data13
import LocalWindowUnsat.CycleWindow4902.Data14
import LocalWindowUnsat.CycleWindow4902.Data15
import LocalWindowUnsat.CycleWindow4902.Data16
import LocalWindowUnsat.CycleWindow4902.Data17
import LocalWindowUnsat.CycleWindow4902.Data18

/-! Kernel checks of segments 13-18 of `cycle4902` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.CycleWindow4902
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok13 : check start13 proof13 = true := by
  decide +kernel

theorem ok14 : check start14 proof14 = true := by
  decide +kernel

theorem ok15 : check start15 proof15 = true := by
  decide +kernel

theorem ok16 : andB (check start16 proof16) (cpOk (replay start16 proof16) start17) = true := by
  decide +kernel

theorem ok17 : check start17 proof17 = true := by
  decide +kernel

theorem ok18 : andB (check start18 proof18) (hasEmpty (replay start18 proof18) 2048) = true := by
  decide +kernel

end Snake9.LocalWindow.CycleWindow4902
