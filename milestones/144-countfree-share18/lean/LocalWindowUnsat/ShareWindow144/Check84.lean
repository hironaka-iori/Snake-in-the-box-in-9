import LocalWindowUnsat.ShareWindow144.Data84
import LocalWindowUnsat.ShareWindow144.Data85

/-! Kernel checks of segments 333-336 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok333 : check start333 proof333 = true := by
  decide +kernel

theorem ok334 : check start334 proof334 = true := by
  decide +kernel

theorem ok335 : check start335 proof335 = true := by
  decide +kernel

theorem ok336 : andB (check start336 proof336) (cpOk (replay start336 proof336) start337) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
