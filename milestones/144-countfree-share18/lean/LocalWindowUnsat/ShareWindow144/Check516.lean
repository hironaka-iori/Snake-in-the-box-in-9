import LocalWindowUnsat.ShareWindow144.Data516
import LocalWindowUnsat.ShareWindow144.Data517

/-! Kernel checks of segments 2061-2064 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok2061 : check start2061 proof2061 = true := by
  decide +kernel

theorem ok2062 : check start2062 proof2062 = true := by
  decide +kernel

theorem ok2063 : check start2063 proof2063 = true := by
  decide +kernel

theorem ok2064 : andB (check start2064 proof2064) (cpOk (replay start2064 proof2064) start2065) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
