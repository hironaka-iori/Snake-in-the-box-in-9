import LocalWindowUnsat.ShareWindow144.Data589
import LocalWindowUnsat.ShareWindow144.Data590

/-! Kernel checks of segments 2353-2356 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok2353 : check start2353 proof2353 = true := by
  decide +kernel

theorem ok2354 : check start2354 proof2354 = true := by
  decide +kernel

theorem ok2355 : check start2355 proof2355 = true := by
  decide +kernel

theorem ok2356 : andB (check start2356 proof2356) (cpOk (replay start2356 proof2356) start2357) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
