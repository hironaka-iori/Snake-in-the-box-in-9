import LocalWindowUnsat.JointSum2.Data72
import LocalWindowUnsat.JointSum2.Data73
import LocalWindowUnsat.JointSum2.Data74
import LocalWindowUnsat.JointSum2.Data75
import LocalWindowUnsat.JointSum2.Data76
import LocalWindowUnsat.JointSum2.Data77
import LocalWindowUnsat.JointSum2.Data78

/-! Kernel checks of segments 73-78 of `sum2` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.JointSum2
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok73 : check start73 proof73 = true := by
  decide +kernel

theorem ok74 : check start74 proof74 = true := by
  decide +kernel

theorem ok75 : check start75 proof75 = true := by
  decide +kernel

theorem ok76 : andB (check start76 proof76) (cpOk (replay start76 proof76) start77) = true := by
  decide +kernel

theorem ok77 : check start77 proof77 = true := by
  decide +kernel

theorem ok78 : check start78 proof78 = true := by
  decide +kernel

end Snake9.LocalWindow.JointSum2
