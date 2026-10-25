import LocalWindowUnsat.JointIntervening501.Data342
import LocalWindowUnsat.JointIntervening501.Data343
import LocalWindowUnsat.JointIntervening501.Data344
import LocalWindowUnsat.JointIntervening501.Data345
import LocalWindowUnsat.JointIntervening501.Data346
import LocalWindowUnsat.JointIntervening501.Data347
import LocalWindowUnsat.JointIntervening501.Data348

/-! Kernel checks of segments 343-348 of `sum501` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.JointIntervening501
open Snake9.LratFast14
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok343 : check start343 proof343 = true := by
  decide +kernel

theorem ok344 : andB (check start344 proof344) (cpOk (replay start344 proof344) start345) = true := by
  decide +kernel

theorem ok345 : check start345 proof345 = true := by
  decide +kernel

theorem ok346 : check start346 proof346 = true := by
  decide +kernel

theorem ok347 : check start347 proof347 = true := by
  decide +kernel

theorem ok348 : andB (check start348 proof348) (cpOk (replay start348 proof348) start349) = true := by
  decide +kernel

end Snake9.LocalWindow.JointIntervening501
