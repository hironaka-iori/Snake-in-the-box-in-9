import LocalWindowUnsat.End35.Data56
import LocalWindowUnsat.End35.Data57

/-! Kernel checks of segments 331-336 of `end35` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.End35
open Snake9.LratFastEndpoint122
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok331 : check start331 proof331 = true := by
  decide +kernel

theorem ok332 : check start332 proof332 = true := by
  decide +kernel

theorem ok333 : check start333 proof333 = true := by
  decide +kernel

theorem ok334 : check start334 proof334 = true := by
  decide +kernel

theorem ok335 : check start335 proof335 = true := by
  decide +kernel

theorem ok336 : andB (check start336 proof336) (cpOk (replay start336 proof336) start337) = true := by
  decide +kernel

end Snake9.LocalWindow.End35
