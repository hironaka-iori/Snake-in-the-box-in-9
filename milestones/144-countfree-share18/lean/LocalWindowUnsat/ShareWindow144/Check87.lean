import LocalWindowUnsat.ShareWindow144.Data87
import LocalWindowUnsat.ShareWindow144.Data88

/-! Kernel checks of segments 345-348 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok345 : check start345 proof345 = true := by
  decide +kernel

theorem ok346 : check start346 proof346 = true := by
  decide +kernel

theorem ok347 : check start347 proof347 = true := by
  decide +kernel

theorem ok348 : andB (check start348 proof348) (cpOk (replay start348 proof348) start349) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
