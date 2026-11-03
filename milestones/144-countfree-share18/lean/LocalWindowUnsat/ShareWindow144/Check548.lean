import LocalWindowUnsat.ShareWindow144.Data548
import LocalWindowUnsat.ShareWindow144.Data549

/-! Kernel checks of segments 2189-2192 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok2189 : check start2189 proof2189 = true := by
  decide +kernel

theorem ok2190 : check start2190 proof2190 = true := by
  decide +kernel

theorem ok2191 : check start2191 proof2191 = true := by
  decide +kernel

theorem ok2192 : andB (check start2192 proof2192) (cpOk (replay start2192 proof2192) start2193) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
