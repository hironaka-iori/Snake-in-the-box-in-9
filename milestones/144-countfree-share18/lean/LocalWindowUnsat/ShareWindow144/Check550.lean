import LocalWindowUnsat.ShareWindow144.Data550
import LocalWindowUnsat.ShareWindow144.Data551

/-! Kernel checks of segments 2197-2200 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok2197 : check start2197 proof2197 = true := by
  decide +kernel

theorem ok2198 : check start2198 proof2198 = true := by
  decide +kernel

theorem ok2199 : check start2199 proof2199 = true := by
  decide +kernel

theorem ok2200 : andB (check start2200 proof2200) (cpOk (replay start2200 proof2200) start2201) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
