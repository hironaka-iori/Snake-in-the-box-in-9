import LocalWindowUnsat.JointIntervening501.Data90
import LocalWindowUnsat.JointIntervening501.Data91
import LocalWindowUnsat.JointIntervening501.Data92
import LocalWindowUnsat.JointIntervening501.Data93
import LocalWindowUnsat.JointIntervening501.Data94
import LocalWindowUnsat.JointIntervening501.Data95
import LocalWindowUnsat.JointIntervening501.Data96

/-! Kernel checks of segments 91-96 of `sum501` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.JointIntervening501
open Snake9.LratFast14
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok91 : check start91 proof91 = true := by
  decide +kernel

theorem ok92 : andB (check start92 proof92) (cpOk (replay start92 proof92) start93) = true := by
  decide +kernel

theorem ok93 : check start93 proof93 = true := by
  decide +kernel

theorem ok94 : check start94 proof94 = true := by
  decide +kernel

theorem ok95 : check start95 proof95 = true := by
  decide +kernel

theorem ok96 : andB (check start96 proof96) (cpOk (replay start96 proof96) start97) = true := by
  decide +kernel

end Snake9.LocalWindow.JointIntervening501
