import LocalWindowUnsat.JointIntervening501.Data300
import LocalWindowUnsat.JointIntervening501.Data301
import LocalWindowUnsat.JointIntervening501.Data302
import LocalWindowUnsat.JointIntervening501.Data303
import LocalWindowUnsat.JointIntervening501.Data304
import LocalWindowUnsat.JointIntervening501.Data305
import LocalWindowUnsat.JointIntervening501.Data306

/-! Kernel checks of segments 301-306 of `sum501` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.JointIntervening501
open Snake9.LratFast14
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok301 : check start301 proof301 = true := by
  decide +kernel

theorem ok302 : check start302 proof302 = true := by
  decide +kernel

theorem ok303 : check start303 proof303 = true := by
  decide +kernel

theorem ok304 : andB (check start304 proof304) (cpOk (replay start304 proof304) start305) = true := by
  decide +kernel

theorem ok305 : check start305 proof305 = true := by
  decide +kernel

theorem ok306 : check start306 proof306 = true := by
  decide +kernel

end Snake9.LocalWindow.JointIntervening501
