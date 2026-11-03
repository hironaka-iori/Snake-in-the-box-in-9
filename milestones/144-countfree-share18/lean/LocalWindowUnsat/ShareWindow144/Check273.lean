import LocalWindowUnsat.ShareWindow144.Data273
import LocalWindowUnsat.ShareWindow144.Data274

/-! Kernel checks of segments 1089-1092 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1089 : check start1089 proof1089 = true := by
  decide +kernel

theorem ok1090 : check start1090 proof1090 = true := by
  decide +kernel

theorem ok1091 : check start1091 proof1091 = true := by
  decide +kernel

theorem ok1092 : andB (check start1092 proof1092) (cpOk (replay start1092 proof1092) start1093) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
