import LocalWindowUnsat.JointIntervening501.Data336
import LocalWindowUnsat.JointIntervening501.Data337
import LocalWindowUnsat.JointIntervening501.Data338
import LocalWindowUnsat.JointIntervening501.Data339
import LocalWindowUnsat.JointIntervening501.Data340
import LocalWindowUnsat.JointIntervening501.Data341
import LocalWindowUnsat.JointIntervening501.Data342

/-! Kernel checks of segments 337-342 of `sum501` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.JointIntervening501
open Snake9.LratFast14
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok337 : check start337 proof337 = true := by
  decide +kernel

theorem ok338 : check start338 proof338 = true := by
  decide +kernel

theorem ok339 : check start339 proof339 = true := by
  decide +kernel

theorem ok340 : andB (check start340 proof340) (cpOk (replay start340 proof340) start341) = true := by
  decide +kernel

theorem ok341 : check start341 proof341 = true := by
  decide +kernel

theorem ok342 : check start342 proof342 = true := by
  decide +kernel

end Snake9.LocalWindow.JointIntervening501
