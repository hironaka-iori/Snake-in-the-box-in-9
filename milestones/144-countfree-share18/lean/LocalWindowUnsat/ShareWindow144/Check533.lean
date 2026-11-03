import LocalWindowUnsat.ShareWindow144.Data533
import LocalWindowUnsat.ShareWindow144.Data534

/-! Kernel checks of segments 2129-2132 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok2129 : check start2129 proof2129 = true := by
  decide +kernel

theorem ok2130 : check start2130 proof2130 = true := by
  decide +kernel

theorem ok2131 : check start2131 proof2131 = true := by
  decide +kernel

theorem ok2132 : andB (check start2132 proof2132) (cpOk (replay start2132 proof2132) start2133) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
