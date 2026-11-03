import LocalWindowUnsat.ShareWindow144.Data91
import LocalWindowUnsat.ShareWindow144.Data92

/-! Kernel checks of segments 361-364 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok361 : check start361 proof361 = true := by
  decide +kernel

theorem ok362 : check start362 proof362 = true := by
  decide +kernel

theorem ok363 : check start363 proof363 = true := by
  decide +kernel

theorem ok364 : andB (check start364 proof364) (cpOk (replay start364 proof364) start365) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
