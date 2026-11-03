import LocalWindowUnsat.ShareWindow144.Data303
import LocalWindowUnsat.ShareWindow144.Data304

/-! Kernel checks of segments 1209-1212 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1209 : check start1209 proof1209 = true := by
  decide +kernel

theorem ok1210 : check start1210 proof1210 = true := by
  decide +kernel

theorem ok1211 : check start1211 proof1211 = true := by
  decide +kernel

theorem ok1212 : andB (check start1212 proof1212) (cpOk (replay start1212 proof1212) start1213) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
