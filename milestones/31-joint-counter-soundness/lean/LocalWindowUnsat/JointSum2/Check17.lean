import LocalWindowUnsat.JointSum2.Data96
import LocalWindowUnsat.JointSum2.Data97
import LocalWindowUnsat.JointSum2.Data98

/-! Kernel checks of segments 97-98 of `sum2` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.JointSum2
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok97 : check start97 proof97 = true := by
  decide +kernel

theorem ok98 : andB (check start98 proof98) (hasEmpty (replay start98 proof98) 4096) = true := by
  decide +kernel

end Snake9.LocalWindow.JointSum2
