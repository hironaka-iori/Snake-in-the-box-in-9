import LocalWindowUnsat.JointIntervening501.Data288
import LocalWindowUnsat.JointIntervening501.Data289
import LocalWindowUnsat.JointIntervening501.Data290
import LocalWindowUnsat.JointIntervening501.Data291
import LocalWindowUnsat.JointIntervening501.Data292
import LocalWindowUnsat.JointIntervening501.Data293
import LocalWindowUnsat.JointIntervening501.Data294

/-! Kernel checks of segments 289-294 of `sum501` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.JointIntervening501
open Snake9.LratFast14
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok289 : check start289 proof289 = true := by
  decide +kernel

theorem ok290 : check start290 proof290 = true := by
  decide +kernel

theorem ok291 : check start291 proof291 = true := by
  decide +kernel

theorem ok292 : andB (check start292 proof292) (cpOk (replay start292 proof292) start293) = true := by
  decide +kernel

theorem ok293 : check start293 proof293 = true := by
  decide +kernel

theorem ok294 : check start294 proof294 = true := by
  decide +kernel

end Snake9.LocalWindow.JointIntervening501
