import LocalWindowUnsat.ShareWindow144.Data35
import LocalWindowUnsat.ShareWindow144.Data36

/-! Kernel checks of segments 137-140 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok137 : check start137 proof137 = true := by
  decide +kernel

theorem ok138 : check start138 proof138 = true := by
  decide +kernel

theorem ok139 : check start139 proof139 = true := by
  decide +kernel

theorem ok140 : andB (check start140 proof140) (cpOk (replay start140 proof140) start141) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
