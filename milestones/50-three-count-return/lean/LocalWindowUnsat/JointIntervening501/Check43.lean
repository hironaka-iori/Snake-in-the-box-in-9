import LocalWindowUnsat.JointIntervening501.Data252
import LocalWindowUnsat.JointIntervening501.Data253
import LocalWindowUnsat.JointIntervening501.Data254
import LocalWindowUnsat.JointIntervening501.Data255
import LocalWindowUnsat.JointIntervening501.Data256
import LocalWindowUnsat.JointIntervening501.Data257
import LocalWindowUnsat.JointIntervening501.Data258

/-! Kernel checks of segments 253-258 of `sum501` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.JointIntervening501
open Snake9.LratFast14
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok253 : check start253 proof253 = true := by
  decide +kernel

theorem ok254 : check start254 proof254 = true := by
  decide +kernel

theorem ok255 : check start255 proof255 = true := by
  decide +kernel

theorem ok256 : andB (check start256 proof256) (cpOk (replay start256 proof256) start257) = true := by
  decide +kernel

theorem ok257 : check start257 proof257 = true := by
  decide +kernel

theorem ok258 : check start258 proof258 = true := by
  decide +kernel

end Snake9.LocalWindow.JointIntervening501
