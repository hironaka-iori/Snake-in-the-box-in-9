import LocalWindowUnsat.ShareWindow144.Data313
import LocalWindowUnsat.ShareWindow144.Data314

/-! Kernel checks of segments 1249-1252 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1249 : check start1249 proof1249 = true := by
  decide +kernel

theorem ok1250 : check start1250 proof1250 = true := by
  decide +kernel

theorem ok1251 : check start1251 proof1251 = true := by
  decide +kernel

theorem ok1252 : andB (check start1252 proof1252) (cpOk (replay start1252 proof1252) start1253) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
