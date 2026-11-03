import LocalWindowUnsat.ShareWindow144.Data209
import LocalWindowUnsat.ShareWindow144.Data210

/-! Kernel checks of segments 833-836 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok833 : check start833 proof833 = true := by
  decide +kernel

theorem ok834 : check start834 proof834 = true := by
  decide +kernel

theorem ok835 : check start835 proof835 = true := by
  decide +kernel

theorem ok836 : andB (check start836 proof836) (cpOk (replay start836 proof836) start837) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
