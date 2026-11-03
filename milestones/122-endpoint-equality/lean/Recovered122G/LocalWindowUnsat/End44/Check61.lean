import Recovered122G.LocalWindowUnsat.End44.Data61
import Recovered122G.LocalWindowUnsat.End44.Data62

/-! Kernel checks of segments 361-366 of `end44` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.End44
open Snake9.LratFastEndpoint122
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok361 : check start361 proof361 = true := by
  decide +kernel

theorem ok362 : check start362 proof362 = true := by
  decide +kernel

theorem ok363 : check start363 proof363 = true := by
  decide +kernel

theorem ok364 : check start364 proof364 = true := by
  decide +kernel

theorem ok365 : check start365 proof365 = true := by
  decide +kernel

theorem ok366 : andB (check start366 proof366) (cpOk (replay start366 proof366) start367) = true := by
  decide +kernel

end Snake9.LocalWindow.End44
