import LocalWindowUnsat.JointIntervening501.Data120
import LocalWindowUnsat.JointIntervening501.Data121
import LocalWindowUnsat.JointIntervening501.Data122
import LocalWindowUnsat.JointIntervening501.Data123
import LocalWindowUnsat.JointIntervening501.Data124
import LocalWindowUnsat.JointIntervening501.Data125
import LocalWindowUnsat.JointIntervening501.Data126

/-! Kernel checks of segments 121-126 of `sum501` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.JointIntervening501
open Snake9.LratFast14
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok121 : check start121 proof121 = true := by
  decide +kernel

theorem ok122 : check start122 proof122 = true := by
  decide +kernel

theorem ok123 : check start123 proof123 = true := by
  decide +kernel

theorem ok124 : andB (check start124 proof124) (cpOk (replay start124 proof124) start125) = true := by
  decide +kernel

theorem ok125 : check start125 proof125 = true := by
  decide +kernel

theorem ok126 : check start126 proof126 = true := by
  decide +kernel

end Snake9.LocalWindow.JointIntervening501
