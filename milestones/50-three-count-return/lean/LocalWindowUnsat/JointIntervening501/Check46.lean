import LocalWindowUnsat.JointIntervening501.Data270
import LocalWindowUnsat.JointIntervening501.Data271
import LocalWindowUnsat.JointIntervening501.Data272
import LocalWindowUnsat.JointIntervening501.Data273
import LocalWindowUnsat.JointIntervening501.Data274
import LocalWindowUnsat.JointIntervening501.Data275
import LocalWindowUnsat.JointIntervening501.Data276

/-! Kernel checks of segments 271-276 of `sum501` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.JointIntervening501
open Snake9.LratFast14
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok271 : check start271 proof271 = true := by
  decide +kernel

theorem ok272 : andB (check start272 proof272) (cpOk (replay start272 proof272) start273) = true := by
  decide +kernel

theorem ok273 : check start273 proof273 = true := by
  decide +kernel

theorem ok274 : check start274 proof274 = true := by
  decide +kernel

theorem ok275 : check start275 proof275 = true := by
  decide +kernel

theorem ok276 : andB (check start276 proof276) (cpOk (replay start276 proof276) start277) = true := by
  decide +kernel

end Snake9.LocalWindow.JointIntervening501
