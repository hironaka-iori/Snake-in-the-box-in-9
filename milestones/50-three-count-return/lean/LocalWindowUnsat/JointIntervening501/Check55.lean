import LocalWindowUnsat.JointIntervening501.Data324
import LocalWindowUnsat.JointIntervening501.Data325
import LocalWindowUnsat.JointIntervening501.Data326
import LocalWindowUnsat.JointIntervening501.Data327
import LocalWindowUnsat.JointIntervening501.Data328
import LocalWindowUnsat.JointIntervening501.Data329
import LocalWindowUnsat.JointIntervening501.Data330

/-! Kernel checks of segments 325-330 of `sum501` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.JointIntervening501
open Snake9.LratFast14
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok325 : check start325 proof325 = true := by
  decide +kernel

theorem ok326 : check start326 proof326 = true := by
  decide +kernel

theorem ok327 : check start327 proof327 = true := by
  decide +kernel

theorem ok328 : andB (check start328 proof328) (cpOk (replay start328 proof328) start329) = true := by
  decide +kernel

theorem ok329 : check start329 proof329 = true := by
  decide +kernel

theorem ok330 : check start330 proof330 = true := by
  decide +kernel

end Snake9.LocalWindow.JointIntervening501
