import LocalWindowUnsat.JointIntervening411.Data102
import LocalWindowUnsat.JointIntervening411.Data103
import LocalWindowUnsat.JointIntervening411.Data104
import LocalWindowUnsat.JointIntervening411.Data105
import LocalWindowUnsat.JointIntervening411.Data106
import LocalWindowUnsat.JointIntervening411.Data107
import LocalWindowUnsat.JointIntervening411.Data108

/-! Kernel checks of segments 103-108 of `sum411` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.JointIntervening411
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok103 : check start103 proof103 = true := by
  decide +kernel

theorem ok104 : andB (check start104 proof104) (cpOk (replay start104 proof104) start105) = true := by
  decide +kernel

theorem ok105 : check start105 proof105 = true := by
  decide +kernel

theorem ok106 : check start106 proof106 = true := by
  decide +kernel

theorem ok107 : check start107 proof107 = true := by
  decide +kernel

theorem ok108 : andB (check start108 proof108) (cpOk (replay start108 proof108) start109) = true := by
  decide +kernel

end Snake9.LocalWindow.JointIntervening411
