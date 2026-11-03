import LocalWindowUnsat.ShareWindow144.Data563
import LocalWindowUnsat.ShareWindow144.Data564

/-! Kernel checks of segments 2249-2252 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok2249 : check start2249 proof2249 = true := by
  decide +kernel

theorem ok2250 : check start2250 proof2250 = true := by
  decide +kernel

theorem ok2251 : check start2251 proof2251 = true := by
  decide +kernel

theorem ok2252 : andB (check start2252 proof2252) (cpOk (replay start2252 proof2252) start2253) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
