import LocalWindowUnsat.JointIntervening501.Data228
import LocalWindowUnsat.JointIntervening501.Data229
import LocalWindowUnsat.JointIntervening501.Data230
import LocalWindowUnsat.JointIntervening501.Data231
import LocalWindowUnsat.JointIntervening501.Data232
import LocalWindowUnsat.JointIntervening501.Data233
import LocalWindowUnsat.JointIntervening501.Data234

/-! Kernel checks of segments 229-234 of `sum501` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.JointIntervening501
open Snake9.LratFast14
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok229 : check start229 proof229 = true := by
  decide +kernel

theorem ok230 : check start230 proof230 = true := by
  decide +kernel

theorem ok231 : check start231 proof231 = true := by
  decide +kernel

theorem ok232 : andB (check start232 proof232) (cpOk (replay start232 proof232) start233) = true := by
  decide +kernel

theorem ok233 : check start233 proof233 = true := by
  decide +kernel

theorem ok234 : check start234 proof234 = true := by
  decide +kernel

end Snake9.LocalWindow.JointIntervening501
