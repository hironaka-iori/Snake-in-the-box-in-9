import LocalWindowUnsat.ShareWindow144.Data578
import LocalWindowUnsat.ShareWindow144.Data579

/-! Kernel checks of segments 2309-2312 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok2309 : check start2309 proof2309 = true := by
  decide +kernel

theorem ok2310 : check start2310 proof2310 = true := by
  decide +kernel

theorem ok2311 : check start2311 proof2311 = true := by
  decide +kernel

theorem ok2312 : andB (check start2312 proof2312) (cpOk (replay start2312 proof2312) start2313) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
