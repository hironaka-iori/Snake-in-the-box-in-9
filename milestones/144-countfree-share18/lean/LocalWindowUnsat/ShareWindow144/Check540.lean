import LocalWindowUnsat.ShareWindow144.Data540
import LocalWindowUnsat.ShareWindow144.Data541

/-! Kernel checks of segments 2157-2160 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok2157 : check start2157 proof2157 = true := by
  decide +kernel

theorem ok2158 : check start2158 proof2158 = true := by
  decide +kernel

theorem ok2159 : check start2159 proof2159 = true := by
  decide +kernel

theorem ok2160 : andB (check start2160 proof2160) (cpOk (replay start2160 proof2160) start2161) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
