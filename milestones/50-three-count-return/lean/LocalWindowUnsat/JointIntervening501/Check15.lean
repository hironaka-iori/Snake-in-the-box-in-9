import LocalWindowUnsat.JointIntervening501.Data84
import LocalWindowUnsat.JointIntervening501.Data85
import LocalWindowUnsat.JointIntervening501.Data86
import LocalWindowUnsat.JointIntervening501.Data87
import LocalWindowUnsat.JointIntervening501.Data88
import LocalWindowUnsat.JointIntervening501.Data89
import LocalWindowUnsat.JointIntervening501.Data90

/-! Kernel checks of segments 85-90 of `sum501` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.JointIntervening501
open Snake9.LratFast14
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok85 : check start85 proof85 = true := by
  decide +kernel

theorem ok86 : check start86 proof86 = true := by
  decide +kernel

theorem ok87 : check start87 proof87 = true := by
  decide +kernel

theorem ok88 : andB (check start88 proof88) (cpOk (replay start88 proof88) start89) = true := by
  decide +kernel

theorem ok89 : check start89 proof89 = true := by
  decide +kernel

theorem ok90 : check start90 proof90 = true := by
  decide +kernel

end Snake9.LocalWindow.JointIntervening501
