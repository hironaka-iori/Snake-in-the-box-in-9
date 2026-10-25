import LocalWindowUnsat.JointIntervening501.Data264
import LocalWindowUnsat.JointIntervening501.Data265
import LocalWindowUnsat.JointIntervening501.Data266
import LocalWindowUnsat.JointIntervening501.Data267
import LocalWindowUnsat.JointIntervening501.Data268
import LocalWindowUnsat.JointIntervening501.Data269
import LocalWindowUnsat.JointIntervening501.Data270

/-! Kernel checks of segments 265-270 of `sum501` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.JointIntervening501
open Snake9.LratFast14
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok265 : check start265 proof265 = true := by
  decide +kernel

theorem ok266 : check start266 proof266 = true := by
  decide +kernel

theorem ok267 : check start267 proof267 = true := by
  decide +kernel

theorem ok268 : andB (check start268 proof268) (cpOk (replay start268 proof268) start269) = true := by
  decide +kernel

theorem ok269 : check start269 proof269 = true := by
  decide +kernel

theorem ok270 : check start270 proof270 = true := by
  decide +kernel

end Snake9.LocalWindow.JointIntervening501
