import LocalWindowUnsat.ShareWindow144.Data236
import LocalWindowUnsat.ShareWindow144.Data237

/-! Kernel checks of segments 941-944 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok941 : check start941 proof941 = true := by
  decide +kernel

theorem ok942 : check start942 proof942 = true := by
  decide +kernel

theorem ok943 : check start943 proof943 = true := by
  decide +kernel

theorem ok944 : andB (check start944 proof944) (cpOk (replay start944 proof944) start945) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
