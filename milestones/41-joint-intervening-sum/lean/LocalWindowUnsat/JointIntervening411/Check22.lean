import LocalWindowUnsat.JointIntervening411.Data126
import LocalWindowUnsat.JointIntervening411.Data127
import LocalWindowUnsat.JointIntervening411.Data128
import LocalWindowUnsat.JointIntervening411.Data129
import LocalWindowUnsat.JointIntervening411.Data130
import LocalWindowUnsat.JointIntervening411.Data131
import LocalWindowUnsat.JointIntervening411.Data132

/-! Kernel checks of segments 127-132 of `sum411` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.JointIntervening411
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok127 : check start127 proof127 = true := by
  decide +kernel

theorem ok128 : andB (check start128 proof128) (cpOk (replay start128 proof128) start129) = true := by
  decide +kernel

theorem ok129 : check start129 proof129 = true := by
  decide +kernel

theorem ok130 : check start130 proof130 = true := by
  decide +kernel

theorem ok131 : check start131 proof131 = true := by
  decide +kernel

theorem ok132 : andB (check start132 proof132) (cpOk (replay start132 proof132) start133) = true := by
  decide +kernel

end Snake9.LocalWindow.JointIntervening411
