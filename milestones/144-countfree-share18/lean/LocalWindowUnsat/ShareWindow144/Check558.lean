import LocalWindowUnsat.ShareWindow144.Data558
import LocalWindowUnsat.ShareWindow144.Data559

/-! Kernel checks of segments 2229-2232 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok2229 : check start2229 proof2229 = true := by
  decide +kernel

theorem ok2230 : check start2230 proof2230 = true := by
  decide +kernel

theorem ok2231 : check start2231 proof2231 = true := by
  decide +kernel

theorem ok2232 : andB (check start2232 proof2232) (cpOk (replay start2232 proof2232) start2233) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
