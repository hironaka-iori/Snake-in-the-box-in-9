import LocalWindowUnsat.CoarseCount2.Data54
import LocalWindowUnsat.CoarseCount2.Data55
import LocalWindowUnsat.CoarseCount2.Data56

/-! Kernel checks of segments 55-56 of `coarse2` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.CoarseCount2
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok55 : check start55 proof55 = true := by
  decide +kernel

theorem ok56 : andB (check start56 proof56) (hasEmpty (replay start56 proof56) 4096) = true := by
  decide +kernel

end Snake9.LocalWindow.CoarseCount2
