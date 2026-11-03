import LocalWindowUnsat.ShareWindow144.Data534
import LocalWindowUnsat.ShareWindow144.Data535

/-! Kernel checks of segments 2133-2136 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok2133 : check start2133 proof2133 = true := by
  decide +kernel

theorem ok2134 : check start2134 proof2134 = true := by
  decide +kernel

theorem ok2135 : check start2135 proof2135 = true := by
  decide +kernel

theorem ok2136 : andB (check start2136 proof2136) (cpOk (replay start2136 proof2136) start2137) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
