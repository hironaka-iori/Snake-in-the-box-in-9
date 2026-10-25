import LocalWindowUnsat.JointIntervening501.Data258
import LocalWindowUnsat.JointIntervening501.Data259
import LocalWindowUnsat.JointIntervening501.Data260
import LocalWindowUnsat.JointIntervening501.Data261
import LocalWindowUnsat.JointIntervening501.Data262
import LocalWindowUnsat.JointIntervening501.Data263
import LocalWindowUnsat.JointIntervening501.Data264

/-! Kernel checks of segments 259-264 of `sum501` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.JointIntervening501
open Snake9.LratFast14
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok259 : check start259 proof259 = true := by
  decide +kernel

theorem ok260 : andB (check start260 proof260) (cpOk (replay start260 proof260) start261) = true := by
  decide +kernel

theorem ok261 : check start261 proof261 = true := by
  decide +kernel

theorem ok262 : check start262 proof262 = true := by
  decide +kernel

theorem ok263 : check start263 proof263 = true := by
  decide +kernel

theorem ok264 : andB (check start264 proof264) (cpOk (replay start264 proof264) start265) = true := by
  decide +kernel

end Snake9.LocalWindow.JointIntervening501
