import LocalWindowUnsat.End35.Data75
import LocalWindowUnsat.End35.Data76

/-! Kernel checks of segments 445-450 of `end35` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.End35
open Snake9.LratFastEndpoint122
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok445 : check start445 proof445 = true := by
  decide +kernel

theorem ok446 : check start446 proof446 = true := by
  decide +kernel

theorem ok447 : check start447 proof447 = true := by
  decide +kernel

theorem ok448 : check start448 proof448 = true := by
  decide +kernel

theorem ok449 : check start449 proof449 = true := by
  decide +kernel

theorem ok450 : andB (check start450 proof450) (cpOk (replay start450 proof450) start451) = true := by
  decide +kernel

end Snake9.LocalWindow.End35
