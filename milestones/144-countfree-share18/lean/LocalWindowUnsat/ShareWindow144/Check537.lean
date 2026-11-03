import LocalWindowUnsat.ShareWindow144.Data537
import LocalWindowUnsat.ShareWindow144.Data538

/-! Kernel checks of segments 2145-2148 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok2145 : check start2145 proof2145 = true := by
  decide +kernel

theorem ok2146 : check start2146 proof2146 = true := by
  decide +kernel

theorem ok2147 : check start2147 proof2147 = true := by
  decide +kernel

theorem ok2148 : andB (check start2148 proof2148) (cpOk (replay start2148 proof2148) start2149) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
