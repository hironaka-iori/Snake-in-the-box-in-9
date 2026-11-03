import LocalWindowUnsat.ShareWindow144.Data73
import LocalWindowUnsat.ShareWindow144.Data74

/-! Kernel checks of segments 289-292 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok289 : check start289 proof289 = true := by
  decide +kernel

theorem ok290 : check start290 proof290 = true := by
  decide +kernel

theorem ok291 : check start291 proof291 = true := by
  decide +kernel

theorem ok292 : andB (check start292 proof292) (cpOk (replay start292 proof292) start293) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
