import LocalWindowUnsat.JointFour2.Data54
import LocalWindowUnsat.JointFour2.Data55
import LocalWindowUnsat.JointFour2.Data56
import LocalWindowUnsat.JointFour2.Data57
import LocalWindowUnsat.JointFour2.Data58

/-! Kernel checks of segments 55-58 of `joint2` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.JointFour2
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok55 : check start55 proof55 = true := by
  decide +kernel

theorem ok56 : andB (check start56 proof56) (cpOk (replay start56 proof56) start57) = true := by
  decide +kernel

theorem ok57 : check start57 proof57 = true := by
  decide +kernel

theorem ok58 : andB (check start58 proof58) (hasEmpty (replay start58 proof58) 4096) = true := by
  decide +kernel

end Snake9.LocalWindow.JointFour2
