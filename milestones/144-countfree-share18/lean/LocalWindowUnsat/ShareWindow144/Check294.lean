import LocalWindowUnsat.ShareWindow144.Data294
import LocalWindowUnsat.ShareWindow144.Data295

/-! Kernel checks of segments 1173-1176 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1173 : check start1173 proof1173 = true := by
  decide +kernel

theorem ok1174 : check start1174 proof1174 = true := by
  decide +kernel

theorem ok1175 : check start1175 proof1175 = true := by
  decide +kernel

theorem ok1176 : andB (check start1176 proof1176) (cpOk (replay start1176 proof1176) start1177) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
