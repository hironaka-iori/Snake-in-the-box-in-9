import LocalWindowUnsat.ShareWindow144.Data575
import LocalWindowUnsat.ShareWindow144.Data576

/-! Kernel checks of segments 2297-2300 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok2297 : check start2297 proof2297 = true := by
  decide +kernel

theorem ok2298 : check start2298 proof2298 = true := by
  decide +kernel

theorem ok2299 : check start2299 proof2299 = true := by
  decide +kernel

theorem ok2300 : andB (check start2300 proof2300) (cpOk (replay start2300 proof2300) start2301) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
