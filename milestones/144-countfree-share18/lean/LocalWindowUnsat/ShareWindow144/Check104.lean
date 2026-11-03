import LocalWindowUnsat.ShareWindow144.Data104
import LocalWindowUnsat.ShareWindow144.Data105

/-! Kernel checks of segments 413-416 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok413 : check start413 proof413 = true := by
  decide +kernel

theorem ok414 : check start414 proof414 = true := by
  decide +kernel

theorem ok415 : check start415 proof415 = true := by
  decide +kernel

theorem ok416 : andB (check start416 proof416) (cpOk (replay start416 proof416) start417) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
