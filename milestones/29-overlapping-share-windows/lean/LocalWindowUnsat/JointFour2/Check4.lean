import LocalWindowUnsat.JointFour2.Data18
import LocalWindowUnsat.JointFour2.Data19
import LocalWindowUnsat.JointFour2.Data20
import LocalWindowUnsat.JointFour2.Data21
import LocalWindowUnsat.JointFour2.Data22
import LocalWindowUnsat.JointFour2.Data23
import LocalWindowUnsat.JointFour2.Data24

/-! Kernel checks of segments 19-24 of `joint2` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.JointFour2
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok19 : check start19 proof19 = true := by
  decide +kernel

theorem ok20 : andB (check start20 proof20) (cpOk (replay start20 proof20) start21) = true := by
  decide +kernel

theorem ok21 : check start21 proof21 = true := by
  decide +kernel

theorem ok22 : check start22 proof22 = true := by
  decide +kernel

theorem ok23 : check start23 proof23 = true := by
  decide +kernel

theorem ok24 : andB (check start24 proof24) (cpOk (replay start24 proof24) start25) = true := by
  decide +kernel

end Snake9.LocalWindow.JointFour2
