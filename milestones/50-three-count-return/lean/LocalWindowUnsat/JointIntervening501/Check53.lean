import LocalWindowUnsat.JointIntervening501.Data312
import LocalWindowUnsat.JointIntervening501.Data313
import LocalWindowUnsat.JointIntervening501.Data314
import LocalWindowUnsat.JointIntervening501.Data315
import LocalWindowUnsat.JointIntervening501.Data316
import LocalWindowUnsat.JointIntervening501.Data317
import LocalWindowUnsat.JointIntervening501.Data318

/-! Kernel checks of segments 313-318 of `sum501` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.JointIntervening501
open Snake9.LratFast14
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok313 : check start313 proof313 = true := by
  decide +kernel

theorem ok314 : check start314 proof314 = true := by
  decide +kernel

theorem ok315 : check start315 proof315 = true := by
  decide +kernel

theorem ok316 : andB (check start316 proof316) (cpOk (replay start316 proof316) start317) = true := by
  decide +kernel

theorem ok317 : check start317 proof317 = true := by
  decide +kernel

theorem ok318 : check start318 proof318 = true := by
  decide +kernel

end Snake9.LocalWindow.JointIntervening501
