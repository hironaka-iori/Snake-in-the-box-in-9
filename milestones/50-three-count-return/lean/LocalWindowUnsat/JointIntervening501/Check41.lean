import LocalWindowUnsat.JointIntervening501.Data240
import LocalWindowUnsat.JointIntervening501.Data241
import LocalWindowUnsat.JointIntervening501.Data242
import LocalWindowUnsat.JointIntervening501.Data243
import LocalWindowUnsat.JointIntervening501.Data244
import LocalWindowUnsat.JointIntervening501.Data245
import LocalWindowUnsat.JointIntervening501.Data246

/-! Kernel checks of segments 241-246 of `sum501` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.JointIntervening501
open Snake9.LratFast14
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok241 : check start241 proof241 = true := by
  decide +kernel

theorem ok242 : check start242 proof242 = true := by
  decide +kernel

theorem ok243 : check start243 proof243 = true := by
  decide +kernel

theorem ok244 : andB (check start244 proof244) (cpOk (replay start244 proof244) start245) = true := by
  decide +kernel

theorem ok245 : check start245 proof245 = true := by
  decide +kernel

theorem ok246 : check start246 proof246 = true := by
  decide +kernel

end Snake9.LocalWindow.JointIntervening501
