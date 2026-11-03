import LocalWindowUnsat.ShareWindow144.Data157
import LocalWindowUnsat.ShareWindow144.Data158

/-! Kernel checks of segments 625-628 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok625 : check start625 proof625 = true := by
  decide +kernel

theorem ok626 : check start626 proof626 = true := by
  decide +kernel

theorem ok627 : check start627 proof627 = true := by
  decide +kernel

theorem ok628 : andB (check start628 proof628) (cpOk (replay start628 proof628) start629) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
