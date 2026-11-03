import LocalWindowUnsat.ShareWindow144.Data31
import LocalWindowUnsat.ShareWindow144.Data32

/-! Kernel checks of segments 121-124 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok121 : check start121 proof121 = true := by
  decide +kernel

theorem ok122 : check start122 proof122 = true := by
  decide +kernel

theorem ok123 : check start123 proof123 = true := by
  decide +kernel

theorem ok124 : andB (check start124 proof124) (cpOk (replay start124 proof124) start125) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
