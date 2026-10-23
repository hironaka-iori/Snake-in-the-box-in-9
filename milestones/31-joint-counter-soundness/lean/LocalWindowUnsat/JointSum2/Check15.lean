import LocalWindowUnsat.JointSum2.Data84
import LocalWindowUnsat.JointSum2.Data85
import LocalWindowUnsat.JointSum2.Data86
import LocalWindowUnsat.JointSum2.Data87
import LocalWindowUnsat.JointSum2.Data88
import LocalWindowUnsat.JointSum2.Data89
import LocalWindowUnsat.JointSum2.Data90

/-! Kernel checks of segments 85-90 of `sum2` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.JointSum2
open Snake9.LratFast
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

end Snake9.LocalWindow.JointSum2
