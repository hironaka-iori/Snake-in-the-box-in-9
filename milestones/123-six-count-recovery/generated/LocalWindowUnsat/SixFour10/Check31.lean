import LocalWindowUnsat.SixFour10.Data31
import LocalWindowUnsat.SixFour10.Data32

/-! Kernel checks of segments 181-186 of `four10` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.SixFour10
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok181 : check start181 proof181 = true := by
  decide +kernel

theorem ok182 : check start182 proof182 = true := by
  decide +kernel

theorem ok183 : check start183 proof183 = true := by
  decide +kernel

theorem ok184 : check start184 proof184 = true := by
  decide +kernel

theorem ok185 : check start185 proof185 = true := by
  decide +kernel

theorem ok186 : andB (check start186 proof186) (cpOk (replay start186 proof186) start187) = true := by
  decide +kernel

end Snake9.LocalWindow.SixFour10
