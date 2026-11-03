import LocalWindowUnsat.ShareWindow144.Data601
import LocalWindowUnsat.ShareWindow144.Data602

/-! Kernel checks of segments 2401-2404 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok2401 : check start2401 proof2401 = true := by
  decide +kernel

theorem ok2402 : check start2402 proof2402 = true := by
  decide +kernel

theorem ok2403 : check start2403 proof2403 = true := by
  decide +kernel

theorem ok2404 : andB (check start2404 proof2404) (cpOk (replay start2404 proof2404) start2405) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
