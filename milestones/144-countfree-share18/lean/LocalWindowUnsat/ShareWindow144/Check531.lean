import LocalWindowUnsat.ShareWindow144.Data531
import LocalWindowUnsat.ShareWindow144.Data532

/-! Kernel checks of segments 2121-2124 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok2121 : check start2121 proof2121 = true := by
  decide +kernel

theorem ok2122 : check start2122 proof2122 = true := by
  decide +kernel

theorem ok2123 : check start2123 proof2123 = true := by
  decide +kernel

theorem ok2124 : andB (check start2124 proof2124) (cpOk (replay start2124 proof2124) start2125) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
