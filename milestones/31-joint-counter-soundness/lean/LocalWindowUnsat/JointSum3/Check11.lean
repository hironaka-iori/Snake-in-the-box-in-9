import LocalWindowUnsat.JointSum3.Data60
import LocalWindowUnsat.JointSum3.Data61
import LocalWindowUnsat.JointSum3.Data62
import LocalWindowUnsat.JointSum3.Data63
import LocalWindowUnsat.JointSum3.Data64

/-! Kernel checks of segments 61-64 of `sum3` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.JointSum3
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok61 : check start61 proof61 = true := by
  decide +kernel

theorem ok62 : check start62 proof62 = true := by
  decide +kernel

theorem ok63 : check start63 proof63 = true := by
  decide +kernel

theorem ok64 : andB (check start64 proof64) (hasEmpty (replay start64 proof64) 4096) = true := by
  decide +kernel

end Snake9.LocalWindow.JointSum3
