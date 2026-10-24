import LocalWindowUnsat.JointIntervening411.Data96
import LocalWindowUnsat.JointIntervening411.Data97
import LocalWindowUnsat.JointIntervening411.Data98
import LocalWindowUnsat.JointIntervening411.Data99
import LocalWindowUnsat.JointIntervening411.Data100
import LocalWindowUnsat.JointIntervening411.Data101
import LocalWindowUnsat.JointIntervening411.Data102

/-! Kernel checks of segments 97-102 of `sum411` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.JointIntervening411
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok97 : check start97 proof97 = true := by
  decide +kernel

theorem ok98 : check start98 proof98 = true := by
  decide +kernel

theorem ok99 : check start99 proof99 = true := by
  decide +kernel

theorem ok100 : andB (check start100 proof100) (cpOk (replay start100 proof100) start101) = true := by
  decide +kernel

theorem ok101 : check start101 proof101 = true := by
  decide +kernel

theorem ok102 : check start102 proof102 = true := by
  decide +kernel

end Snake9.LocalWindow.JointIntervening411
