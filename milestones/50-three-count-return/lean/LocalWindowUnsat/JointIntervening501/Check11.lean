import LocalWindowUnsat.JointIntervening501.Data60
import LocalWindowUnsat.JointIntervening501.Data61
import LocalWindowUnsat.JointIntervening501.Data62
import LocalWindowUnsat.JointIntervening501.Data63
import LocalWindowUnsat.JointIntervening501.Data64
import LocalWindowUnsat.JointIntervening501.Data65
import LocalWindowUnsat.JointIntervening501.Data66

/-! Kernel checks of segments 61-66 of `sum501` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.JointIntervening501
open Snake9.LratFast14
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok61 : check start61 proof61 = true := by
  decide +kernel

theorem ok62 : check start62 proof62 = true := by
  decide +kernel

theorem ok63 : check start63 proof63 = true := by
  decide +kernel

theorem ok64 : andB (check start64 proof64) (cpOk (replay start64 proof64) start65) = true := by
  decide +kernel

theorem ok65 : check start65 proof65 = true := by
  decide +kernel

theorem ok66 : check start66 proof66 = true := by
  decide +kernel

end Snake9.LocalWindow.JointIntervening501
