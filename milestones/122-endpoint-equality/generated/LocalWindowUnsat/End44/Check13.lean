import LocalWindowUnsat.End44.Data13
import LocalWindowUnsat.End44.Data14

/-! Kernel checks of segments 73-78 of `end44` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.End44
open Snake9.LratFastEndpoint122
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok73 : check start73 proof73 = true := by
  decide +kernel

theorem ok74 : check start74 proof74 = true := by
  decide +kernel

theorem ok75 : check start75 proof75 = true := by
  decide +kernel

theorem ok76 : check start76 proof76 = true := by
  decide +kernel

theorem ok77 : check start77 proof77 = true := by
  decide +kernel

theorem ok78 : andB (check start78 proof78) (cpOk (replay start78 proof78) start79) = true := by
  decide +kernel

end Snake9.LocalWindow.End44
