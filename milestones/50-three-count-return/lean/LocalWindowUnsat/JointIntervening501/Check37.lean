import LocalWindowUnsat.JointIntervening501.Data216
import LocalWindowUnsat.JointIntervening501.Data217
import LocalWindowUnsat.JointIntervening501.Data218
import LocalWindowUnsat.JointIntervening501.Data219
import LocalWindowUnsat.JointIntervening501.Data220
import LocalWindowUnsat.JointIntervening501.Data221
import LocalWindowUnsat.JointIntervening501.Data222

/-! Kernel checks of segments 217-222 of `sum501` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.JointIntervening501
open Snake9.LratFast14
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok217 : check start217 proof217 = true := by
  decide +kernel

theorem ok218 : check start218 proof218 = true := by
  decide +kernel

theorem ok219 : check start219 proof219 = true := by
  decide +kernel

theorem ok220 : andB (check start220 proof220) (cpOk (replay start220 proof220) start221) = true := by
  decide +kernel

theorem ok221 : check start221 proof221 = true := by
  decide +kernel

theorem ok222 : check start222 proof222 = true := by
  decide +kernel

end Snake9.LocalWindow.JointIntervening501
