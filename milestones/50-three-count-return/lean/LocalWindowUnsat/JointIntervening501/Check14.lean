import LocalWindowUnsat.JointIntervening501.Data78
import LocalWindowUnsat.JointIntervening501.Data79
import LocalWindowUnsat.JointIntervening501.Data80
import LocalWindowUnsat.JointIntervening501.Data81
import LocalWindowUnsat.JointIntervening501.Data82
import LocalWindowUnsat.JointIntervening501.Data83
import LocalWindowUnsat.JointIntervening501.Data84

/-! Kernel checks of segments 79-84 of `sum501` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.JointIntervening501
open Snake9.LratFast14
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok79 : check start79 proof79 = true := by
  decide +kernel

theorem ok80 : andB (check start80 proof80) (cpOk (replay start80 proof80) start81) = true := by
  decide +kernel

theorem ok81 : check start81 proof81 = true := by
  decide +kernel

theorem ok82 : check start82 proof82 = true := by
  decide +kernel

theorem ok83 : check start83 proof83 = true := by
  decide +kernel

theorem ok84 : andB (check start84 proof84) (cpOk (replay start84 proof84) start85) = true := by
  decide +kernel

end Snake9.LocalWindow.JointIntervening501
