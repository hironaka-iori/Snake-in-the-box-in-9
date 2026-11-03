import LocalWindowUnsat.ShareWindow144.Data30
import LocalWindowUnsat.ShareWindow144.Data31

/-! Kernel checks of segments 117-120 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok117 : check start117 proof117 = true := by
  decide +kernel

theorem ok118 : check start118 proof118 = true := by
  decide +kernel

theorem ok119 : check start119 proof119 = true := by
  decide +kernel

theorem ok120 : andB (check start120 proof120) (cpOk (replay start120 proof120) start121) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
