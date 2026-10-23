import LocalWindowUnsat.JointSum3.Data24
import LocalWindowUnsat.JointSum3.Data25
import LocalWindowUnsat.JointSum3.Data26
import LocalWindowUnsat.JointSum3.Data27
import LocalWindowUnsat.JointSum3.Data28
import LocalWindowUnsat.JointSum3.Data29
import LocalWindowUnsat.JointSum3.Data30

/-! Kernel checks of segments 25-30 of `sum3` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.JointSum3
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok25 : check start25 proof25 = true := by
  decide +kernel

theorem ok26 : check start26 proof26 = true := by
  decide +kernel

theorem ok27 : check start27 proof27 = true := by
  decide +kernel

theorem ok28 : andB (check start28 proof28) (cpOk (replay start28 proof28) start29) = true := by
  decide +kernel

theorem ok29 : check start29 proof29 = true := by
  decide +kernel

theorem ok30 : check start30 proof30 = true := by
  decide +kernel

end Snake9.LocalWindow.JointSum3
