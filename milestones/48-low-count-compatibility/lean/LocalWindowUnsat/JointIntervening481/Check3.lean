import LocalWindowUnsat.JointIntervening481.Data12
import LocalWindowUnsat.JointIntervening481.Data13

/-! Kernel checks of segments 13-13 of `sum481` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.JointIntervening481
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok13 : andB (check start13 proof13) (hasEmpty (replay start13 proof13) 2048) = true := by
  decide +kernel

end Snake9.LocalWindow.JointIntervening481
