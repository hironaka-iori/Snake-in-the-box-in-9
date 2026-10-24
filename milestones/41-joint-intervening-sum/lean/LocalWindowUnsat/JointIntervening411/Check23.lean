import LocalWindowUnsat.JointIntervening411.Data132
import LocalWindowUnsat.JointIntervening411.Data133
import LocalWindowUnsat.JointIntervening411.Data134
import LocalWindowUnsat.JointIntervening411.Data135
import LocalWindowUnsat.JointIntervening411.Data136
import LocalWindowUnsat.JointIntervening411.Data137
import LocalWindowUnsat.JointIntervening411.Data138

/-! Kernel checks of segments 133-138 of `sum411` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.JointIntervening411
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok133 : check start133 proof133 = true := by
  decide +kernel

theorem ok134 : check start134 proof134 = true := by
  decide +kernel

theorem ok135 : check start135 proof135 = true := by
  decide +kernel

theorem ok136 : andB (check start136 proof136) (cpOk (replay start136 proof136) start137) = true := by
  decide +kernel

theorem ok137 : check start137 proof137 = true := by
  decide +kernel

theorem ok138 : check start138 proof138 = true := by
  decide +kernel

end Snake9.LocalWindow.JointIntervening411
