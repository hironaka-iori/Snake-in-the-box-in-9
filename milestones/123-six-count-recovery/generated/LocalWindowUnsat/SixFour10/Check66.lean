import LocalWindowUnsat.SixFour10.Data66
import LocalWindowUnsat.SixFour10.Data67

/-! Kernel checks of segments 391-396 of `four10` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.SixFour10
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok391 : check start391 proof391 = true := by
  decide +kernel

theorem ok392 : check start392 proof392 = true := by
  decide +kernel

theorem ok393 : check start393 proof393 = true := by
  decide +kernel

theorem ok394 : check start394 proof394 = true := by
  decide +kernel

theorem ok395 : check start395 proof395 = true := by
  decide +kernel

theorem ok396 : andB (check start396 proof396) (cpOk (replay start396 proof396) start397) = true := by
  decide +kernel

end Snake9.LocalWindow.SixFour10
