import LocalWindowUnsat.JointIntervening501.Data348
import LocalWindowUnsat.JointIntervening501.Data349
import LocalWindowUnsat.JointIntervening501.Data350
import LocalWindowUnsat.JointIntervening501.Data351
import LocalWindowUnsat.JointIntervening501.Data352
import LocalWindowUnsat.JointIntervening501.Data353
import LocalWindowUnsat.JointIntervening501.Data354

/-! Kernel checks of segments 349-354 of `sum501` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.JointIntervening501
open Snake9.LratFast14
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok349 : check start349 proof349 = true := by
  decide +kernel

theorem ok350 : check start350 proof350 = true := by
  decide +kernel

theorem ok351 : check start351 proof351 = true := by
  decide +kernel

theorem ok352 : andB (check start352 proof352) (cpOk (replay start352 proof352) start353) = true := by
  decide +kernel

theorem ok353 : check start353 proof353 = true := by
  decide +kernel

theorem ok354 : check start354 proof354 = true := by
  decide +kernel

end Snake9.LocalWindow.JointIntervening501
