import LocalWindowUnsat.ShareWindow144.Data301
import LocalWindowUnsat.ShareWindow144.Data302

/-! Kernel checks of segments 1201-1204 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1201 : check start1201 proof1201 = true := by
  decide +kernel

theorem ok1202 : check start1202 proof1202 = true := by
  decide +kernel

theorem ok1203 : check start1203 proof1203 = true := by
  decide +kernel

theorem ok1204 : andB (check start1204 proof1204) (cpOk (replay start1204 proof1204) start1205) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
