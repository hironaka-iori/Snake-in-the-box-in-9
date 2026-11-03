import LocalWindowUnsat.ShareWindow144.Data95
import LocalWindowUnsat.ShareWindow144.Data96

/-! Kernel checks of segments 377-380 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok377 : check start377 proof377 = true := by
  decide +kernel

theorem ok378 : check start378 proof378 = true := by
  decide +kernel

theorem ok379 : check start379 proof379 = true := by
  decide +kernel

theorem ok380 : andB (check start380 proof380) (cpOk (replay start380 proof380) start381) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
