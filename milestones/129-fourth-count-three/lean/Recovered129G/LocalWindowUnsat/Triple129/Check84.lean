import Recovered129G.LocalWindowUnsat.Triple129.Data84
import Recovered129G.LocalWindowUnsat.Triple129.Data85

/-! Kernel checks of segments 333-336 of `triple129` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Triple129
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok333 : check start333 proof333 = true := by
  decide +kernel

theorem ok334 : check start334 proof334 = true := by
  decide +kernel

theorem ok335 : check start335 proof335 = true := by
  decide +kernel

theorem ok336 : andB (check start336 proof336) (cpOk (replay start336 proof336) start337) = true := by
  decide +kernel

end Snake9.LocalWindow.Triple129
