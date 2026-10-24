import LocalWindowUnsat.JointIntervening411.Data168
import LocalWindowUnsat.JointIntervening411.Data169
import LocalWindowUnsat.JointIntervening411.Data170
import LocalWindowUnsat.JointIntervening411.Data171
import LocalWindowUnsat.JointIntervening411.Data172
import LocalWindowUnsat.JointIntervening411.Data173
import LocalWindowUnsat.JointIntervening411.Data174

/-! Kernel checks of segments 169-174 of `sum411` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.JointIntervening411
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok169 : check start169 proof169 = true := by
  decide +kernel

theorem ok170 : check start170 proof170 = true := by
  decide +kernel

theorem ok171 : check start171 proof171 = true := by
  decide +kernel

theorem ok172 : andB (check start172 proof172) (cpOk (replay start172 proof172) start173) = true := by
  decide +kernel

theorem ok173 : check start173 proof173 = true := by
  decide +kernel

theorem ok174 : andB (check start174 proof174) (hasEmpty (replay start174 proof174) 4096) = true := by
  decide +kernel

end Snake9.LocalWindow.JointIntervening411
