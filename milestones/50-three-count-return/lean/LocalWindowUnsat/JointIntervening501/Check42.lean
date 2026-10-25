import LocalWindowUnsat.JointIntervening501.Data246
import LocalWindowUnsat.JointIntervening501.Data247
import LocalWindowUnsat.JointIntervening501.Data248
import LocalWindowUnsat.JointIntervening501.Data249
import LocalWindowUnsat.JointIntervening501.Data250
import LocalWindowUnsat.JointIntervening501.Data251
import LocalWindowUnsat.JointIntervening501.Data252

/-! Kernel checks of segments 247-252 of `sum501` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.JointIntervening501
open Snake9.LratFast14
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok247 : check start247 proof247 = true := by
  decide +kernel

theorem ok248 : andB (check start248 proof248) (cpOk (replay start248 proof248) start249) = true := by
  decide +kernel

theorem ok249 : check start249 proof249 = true := by
  decide +kernel

theorem ok250 : check start250 proof250 = true := by
  decide +kernel

theorem ok251 : check start251 proof251 = true := by
  decide +kernel

theorem ok252 : andB (check start252 proof252) (cpOk (replay start252 proof252) start253) = true := by
  decide +kernel

end Snake9.LocalWindow.JointIntervening501
