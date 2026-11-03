import LocalWindowUnsat.End44.Data81
import LocalWindowUnsat.End44.Data82

/-! Kernel checks of segments 481-486 of `end44` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.End44
open Snake9.LratFastEndpoint122
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok481 : check start481 proof481 = true := by
  decide +kernel

theorem ok482 : check start482 proof482 = true := by
  decide +kernel

theorem ok483 : check start483 proof483 = true := by
  decide +kernel

theorem ok484 : check start484 proof484 = true := by
  decide +kernel

theorem ok485 : check start485 proof485 = true := by
  decide +kernel

theorem ok486 : andB (check start486 proof486) (cpOk (replay start486 proof486) start487) = true := by
  decide +kernel

end Snake9.LocalWindow.End44
