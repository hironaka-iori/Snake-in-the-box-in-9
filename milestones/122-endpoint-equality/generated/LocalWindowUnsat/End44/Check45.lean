import LocalWindowUnsat.End44.Data45
import LocalWindowUnsat.End44.Data46

/-! Kernel checks of segments 265-270 of `end44` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.End44
open Snake9.LratFastEndpoint122
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok265 : check start265 proof265 = true := by
  decide +kernel

theorem ok266 : check start266 proof266 = true := by
  decide +kernel

theorem ok267 : check start267 proof267 = true := by
  decide +kernel

theorem ok268 : check start268 proof268 = true := by
  decide +kernel

theorem ok269 : check start269 proof269 = true := by
  decide +kernel

theorem ok270 : andB (check start270 proof270) (cpOk (replay start270 proof270) start271) = true := by
  decide +kernel

end Snake9.LocalWindow.End44
