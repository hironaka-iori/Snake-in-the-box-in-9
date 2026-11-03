import LocalWindowUnsat.ShareWindow144.Data150
import LocalWindowUnsat.ShareWindow144.Data151

/-! Kernel checks of segments 597-600 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok597 : check start597 proof597 = true := by
  decide +kernel

theorem ok598 : check start598 proof598 = true := by
  decide +kernel

theorem ok599 : check start599 proof599 = true := by
  decide +kernel

theorem ok600 : andB (check start600 proof600) (cpOk (replay start600 proof600) start601) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
