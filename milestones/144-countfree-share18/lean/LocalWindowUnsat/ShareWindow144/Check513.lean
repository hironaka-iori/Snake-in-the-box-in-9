import LocalWindowUnsat.ShareWindow144.Data513
import LocalWindowUnsat.ShareWindow144.Data514

/-! Kernel checks of segments 2049-2052 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok2049 : check start2049 proof2049 = true := by
  decide +kernel

theorem ok2050 : check start2050 proof2050 = true := by
  decide +kernel

theorem ok2051 : check start2051 proof2051 = true := by
  decide +kernel

theorem ok2052 : andB (check start2052 proof2052) (cpOk (replay start2052 proof2052) start2053) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
