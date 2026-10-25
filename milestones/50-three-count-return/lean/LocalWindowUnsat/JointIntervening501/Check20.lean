import LocalWindowUnsat.JointIntervening501.Data114
import LocalWindowUnsat.JointIntervening501.Data115
import LocalWindowUnsat.JointIntervening501.Data116
import LocalWindowUnsat.JointIntervening501.Data117
import LocalWindowUnsat.JointIntervening501.Data118
import LocalWindowUnsat.JointIntervening501.Data119
import LocalWindowUnsat.JointIntervening501.Data120

/-! Kernel checks of segments 115-120 of `sum501` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.JointIntervening501
open Snake9.LratFast14
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok115 : check start115 proof115 = true := by
  decide +kernel

theorem ok116 : andB (check start116 proof116) (cpOk (replay start116 proof116) start117) = true := by
  decide +kernel

theorem ok117 : check start117 proof117 = true := by
  decide +kernel

theorem ok118 : check start118 proof118 = true := by
  decide +kernel

theorem ok119 : check start119 proof119 = true := by
  decide +kernel

theorem ok120 : andB (check start120 proof120) (cpOk (replay start120 proof120) start121) = true := by
  decide +kernel

end Snake9.LocalWindow.JointIntervening501
