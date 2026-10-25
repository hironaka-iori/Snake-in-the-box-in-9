import LocalWindowUnsat.JointIntervening501.Data54
import LocalWindowUnsat.JointIntervening501.Data55
import LocalWindowUnsat.JointIntervening501.Data56
import LocalWindowUnsat.JointIntervening501.Data57
import LocalWindowUnsat.JointIntervening501.Data58
import LocalWindowUnsat.JointIntervening501.Data59
import LocalWindowUnsat.JointIntervening501.Data60

/-! Kernel checks of segments 55-60 of `sum501` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.JointIntervening501
open Snake9.LratFast14
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok55 : check start55 proof55 = true := by
  decide +kernel

theorem ok56 : andB (check start56 proof56) (cpOk (replay start56 proof56) start57) = true := by
  decide +kernel

theorem ok57 : check start57 proof57 = true := by
  decide +kernel

theorem ok58 : check start58 proof58 = true := by
  decide +kernel

theorem ok59 : check start59 proof59 = true := by
  decide +kernel

theorem ok60 : andB (check start60 proof60) (cpOk (replay start60 proof60) start61) = true := by
  decide +kernel

end Snake9.LocalWindow.JointIntervening501
