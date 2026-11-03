import LocalWindowUnsat.End35.Data74
import LocalWindowUnsat.End35.Data75

/-! Kernel checks of segments 439-444 of `end35` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.End35
open Snake9.LratFastEndpoint122
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok439 : check start439 proof439 = true := by
  decide +kernel

theorem ok440 : check start440 proof440 = true := by
  decide +kernel

theorem ok441 : check start441 proof441 = true := by
  decide +kernel

theorem ok442 : check start442 proof442 = true := by
  decide +kernel

theorem ok443 : check start443 proof443 = true := by
  decide +kernel

theorem ok444 : andB (check start444 proof444) (cpOk (replay start444 proof444) start445) = true := by
  decide +kernel

end Snake9.LocalWindow.End35
