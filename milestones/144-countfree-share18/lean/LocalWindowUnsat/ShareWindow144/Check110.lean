import LocalWindowUnsat.ShareWindow144.Data110
import LocalWindowUnsat.ShareWindow144.Data111

/-! Kernel checks of segments 437-440 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok437 : check start437 proof437 = true := by
  decide +kernel

theorem ok438 : check start438 proof438 = true := by
  decide +kernel

theorem ok439 : check start439 proof439 = true := by
  decide +kernel

theorem ok440 : andB (check start440 proof440) (cpOk (replay start440 proof440) start441) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
