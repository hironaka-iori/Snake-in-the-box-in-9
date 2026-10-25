import LocalWindowUnsat.JointIntervening501.Data180
import LocalWindowUnsat.JointIntervening501.Data181
import LocalWindowUnsat.JointIntervening501.Data182
import LocalWindowUnsat.JointIntervening501.Data183
import LocalWindowUnsat.JointIntervening501.Data184
import LocalWindowUnsat.JointIntervening501.Data185
import LocalWindowUnsat.JointIntervening501.Data186

/-! Kernel checks of segments 181-186 of `sum501` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.JointIntervening501
open Snake9.LratFast14
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok181 : check start181 proof181 = true := by
  decide +kernel

theorem ok182 : check start182 proof182 = true := by
  decide +kernel

theorem ok183 : check start183 proof183 = true := by
  decide +kernel

theorem ok184 : andB (check start184 proof184) (cpOk (replay start184 proof184) start185) = true := by
  decide +kernel

theorem ok185 : check start185 proof185 = true := by
  decide +kernel

theorem ok186 : check start186 proof186 = true := by
  decide +kernel

end Snake9.LocalWindow.JointIntervening501
