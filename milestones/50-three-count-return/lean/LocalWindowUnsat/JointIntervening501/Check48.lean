import LocalWindowUnsat.JointIntervening501.Data282
import LocalWindowUnsat.JointIntervening501.Data283
import LocalWindowUnsat.JointIntervening501.Data284
import LocalWindowUnsat.JointIntervening501.Data285
import LocalWindowUnsat.JointIntervening501.Data286
import LocalWindowUnsat.JointIntervening501.Data287
import LocalWindowUnsat.JointIntervening501.Data288

/-! Kernel checks of segments 283-288 of `sum501` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.JointIntervening501
open Snake9.LratFast14
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok283 : check start283 proof283 = true := by
  decide +kernel

theorem ok284 : andB (check start284 proof284) (cpOk (replay start284 proof284) start285) = true := by
  decide +kernel

theorem ok285 : check start285 proof285 = true := by
  decide +kernel

theorem ok286 : check start286 proof286 = true := by
  decide +kernel

theorem ok287 : check start287 proof287 = true := by
  decide +kernel

theorem ok288 : andB (check start288 proof288) (cpOk (replay start288 proof288) start289) = true := by
  decide +kernel

end Snake9.LocalWindow.JointIntervening501
