import LocalWindowUnsat.ShareWindow144.Data330
import LocalWindowUnsat.ShareWindow144.Data331

/-! Kernel checks of segments 1317-1320 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1317 : check start1317 proof1317 = true := by
  decide +kernel

theorem ok1318 : check start1318 proof1318 = true := by
  decide +kernel

theorem ok1319 : check start1319 proof1319 = true := by
  decide +kernel

theorem ok1320 : andB (check start1320 proof1320) (cpOk (replay start1320 proof1320) start1321) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
