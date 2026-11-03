import LocalWindowUnsat.ShareWindow144.Data70
import LocalWindowUnsat.ShareWindow144.Data71

/-! Kernel checks of segments 277-280 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok277 : check start277 proof277 = true := by
  decide +kernel

theorem ok278 : check start278 proof278 = true := by
  decide +kernel

theorem ok279 : check start279 proof279 = true := by
  decide +kernel

theorem ok280 : andB (check start280 proof280) (cpOk (replay start280 proof280) start281) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
