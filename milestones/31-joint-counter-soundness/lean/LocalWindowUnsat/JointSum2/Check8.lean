import LocalWindowUnsat.JointSum2.Data42
import LocalWindowUnsat.JointSum2.Data43
import LocalWindowUnsat.JointSum2.Data44
import LocalWindowUnsat.JointSum2.Data45
import LocalWindowUnsat.JointSum2.Data46
import LocalWindowUnsat.JointSum2.Data47
import LocalWindowUnsat.JointSum2.Data48

/-! Kernel checks of segments 43-48 of `sum2` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.JointSum2
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok43 : check start43 proof43 = true := by
  decide +kernel

theorem ok44 : andB (check start44 proof44) (cpOk (replay start44 proof44) start45) = true := by
  decide +kernel

theorem ok45 : check start45 proof45 = true := by
  decide +kernel

theorem ok46 : check start46 proof46 = true := by
  decide +kernel

theorem ok47 : check start47 proof47 = true := by
  decide +kernel

theorem ok48 : andB (check start48 proof48) (cpOk (replay start48 proof48) start49) = true := by
  decide +kernel

end Snake9.LocalWindow.JointSum2
