import LocalWindowUnsat.ShareWindow144.Data99
import LocalWindowUnsat.ShareWindow144.Data100

/-! Kernel checks of segments 393-396 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok393 : check start393 proof393 = true := by
  decide +kernel

theorem ok394 : check start394 proof394 = true := by
  decide +kernel

theorem ok395 : check start395 proof395 = true := by
  decide +kernel

theorem ok396 : andB (check start396 proof396) (cpOk (replay start396 proof396) start397) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
