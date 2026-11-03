import LocalWindowUnsat.ShareWindow144.Data552
import LocalWindowUnsat.ShareWindow144.Data553

/-! Kernel checks of segments 2205-2208 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok2205 : check start2205 proof2205 = true := by
  decide +kernel

theorem ok2206 : check start2206 proof2206 = true := by
  decide +kernel

theorem ok2207 : check start2207 proof2207 = true := by
  decide +kernel

theorem ok2208 : andB (check start2208 proof2208) (cpOk (replay start2208 proof2208) start2209) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
