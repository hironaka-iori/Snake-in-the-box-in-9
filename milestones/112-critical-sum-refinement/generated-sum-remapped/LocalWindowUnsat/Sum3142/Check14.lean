import LocalWindowUnsat.Sum3142.Data14
import LocalWindowUnsat.Sum3142.Data15

/-! Kernel checks of segments 53-56 of `sum3142` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Sum3142
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok53 : check start53 proof53 = true := by
  decide +kernel

theorem ok54 : check start54 proof54 = true := by
  decide +kernel

theorem ok55 : check start55 proof55 = true := by
  decide +kernel

theorem ok56 : andB (check start56 proof56) (cpOk (replay start56 proof56) start57) = true := by
  decide +kernel

end Snake9.LocalWindow.Sum3142
