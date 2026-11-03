import LocalWindowUnsat.ShareWindow144.Data237
import LocalWindowUnsat.ShareWindow144.Data238

/-! Kernel checks of segments 945-948 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok945 : check start945 proof945 = true := by
  decide +kernel

theorem ok946 : check start946 proof946 = true := by
  decide +kernel

theorem ok947 : check start947 proof947 = true := by
  decide +kernel

theorem ok948 : andB (check start948 proof948) (cpOk (replay start948 proof948) start949) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
