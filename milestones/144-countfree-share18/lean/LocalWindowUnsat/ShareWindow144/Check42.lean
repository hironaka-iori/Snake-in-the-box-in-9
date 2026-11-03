import LocalWindowUnsat.ShareWindow144.Data42
import LocalWindowUnsat.ShareWindow144.Data43

/-! Kernel checks of segments 165-168 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok165 : check start165 proof165 = true := by
  decide +kernel

theorem ok166 : check start166 proof166 = true := by
  decide +kernel

theorem ok167 : check start167 proof167 = true := by
  decide +kernel

theorem ok168 : andB (check start168 proof168) (cpOk (replay start168 proof168) start169) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
