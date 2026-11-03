import LocalWindowUnsat.ShareWindow144.Data111
import LocalWindowUnsat.ShareWindow144.Data112

/-! Kernel checks of segments 441-444 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok441 : check start441 proof441 = true := by
  decide +kernel

theorem ok442 : check start442 proof442 = true := by
  decide +kernel

theorem ok443 : check start443 proof443 = true := by
  decide +kernel

theorem ok444 : andB (check start444 proof444) (cpOk (replay start444 proof444) start445) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
