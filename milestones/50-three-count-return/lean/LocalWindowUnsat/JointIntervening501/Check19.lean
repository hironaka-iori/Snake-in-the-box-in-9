import LocalWindowUnsat.JointIntervening501.Data108
import LocalWindowUnsat.JointIntervening501.Data109
import LocalWindowUnsat.JointIntervening501.Data110
import LocalWindowUnsat.JointIntervening501.Data111
import LocalWindowUnsat.JointIntervening501.Data112
import LocalWindowUnsat.JointIntervening501.Data113
import LocalWindowUnsat.JointIntervening501.Data114

/-! Kernel checks of segments 109-114 of `sum501` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.JointIntervening501
open Snake9.LratFast14
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok109 : check start109 proof109 = true := by
  decide +kernel

theorem ok110 : check start110 proof110 = true := by
  decide +kernel

theorem ok111 : check start111 proof111 = true := by
  decide +kernel

theorem ok112 : andB (check start112 proof112) (cpOk (replay start112 proof112) start113) = true := by
  decide +kernel

theorem ok113 : check start113 proof113 = true := by
  decide +kernel

theorem ok114 : check start114 proof114 = true := by
  decide +kernel

end Snake9.LocalWindow.JointIntervening501
