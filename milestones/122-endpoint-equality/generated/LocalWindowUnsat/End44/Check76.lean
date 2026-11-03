import LocalWindowUnsat.End44.Data76
import LocalWindowUnsat.End44.Data77

/-! Kernel checks of segments 451-456 of `end44` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.End44
open Snake9.LratFastEndpoint122
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok451 : check start451 proof451 = true := by
  decide +kernel

theorem ok452 : check start452 proof452 = true := by
  decide +kernel

theorem ok453 : check start453 proof453 = true := by
  decide +kernel

theorem ok454 : check start454 proof454 = true := by
  decide +kernel

theorem ok455 : check start455 proof455 = true := by
  decide +kernel

theorem ok456 : andB (check start456 proof456) (cpOk (replay start456 proof456) start457) = true := by
  decide +kernel

end Snake9.LocalWindow.End44
