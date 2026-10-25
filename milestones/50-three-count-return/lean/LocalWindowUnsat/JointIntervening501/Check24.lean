import LocalWindowUnsat.JointIntervening501.Data138
import LocalWindowUnsat.JointIntervening501.Data139
import LocalWindowUnsat.JointIntervening501.Data140
import LocalWindowUnsat.JointIntervening501.Data141
import LocalWindowUnsat.JointIntervening501.Data142
import LocalWindowUnsat.JointIntervening501.Data143
import LocalWindowUnsat.JointIntervening501.Data144

/-! Kernel checks of segments 139-144 of `sum501` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.JointIntervening501
open Snake9.LratFast14
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok139 : check start139 proof139 = true := by
  decide +kernel

theorem ok140 : andB (check start140 proof140) (cpOk (replay start140 proof140) start141) = true := by
  decide +kernel

theorem ok141 : check start141 proof141 = true := by
  decide +kernel

theorem ok142 : check start142 proof142 = true := by
  decide +kernel

theorem ok143 : check start143 proof143 = true := by
  decide +kernel

theorem ok144 : andB (check start144 proof144) (cpOk (replay start144 proof144) start145) = true := by
  decide +kernel

end Snake9.LocalWindow.JointIntervening501
