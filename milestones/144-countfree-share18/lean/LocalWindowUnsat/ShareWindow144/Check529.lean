import LocalWindowUnsat.ShareWindow144.Data529
import LocalWindowUnsat.ShareWindow144.Data530

/-! Kernel checks of segments 2113-2116 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok2113 : check start2113 proof2113 = true := by
  decide +kernel

theorem ok2114 : check start2114 proof2114 = true := by
  decide +kernel

theorem ok2115 : check start2115 proof2115 = true := by
  decide +kernel

theorem ok2116 : andB (check start2116 proof2116) (cpOk (replay start2116 proof2116) start2117) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
