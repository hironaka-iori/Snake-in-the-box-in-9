import Recovered123G.LocalWindowUnsat.SixFour10.Data49
import Recovered123G.LocalWindowUnsat.SixFour10.Data50

/-! Kernel checks of segments 289-294 of `four10` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.SixFour10
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok289 : check start289 proof289 = true := by
  decide +kernel

theorem ok290 : check start290 proof290 = true := by
  decide +kernel

theorem ok291 : check start291 proof291 = true := by
  decide +kernel

theorem ok292 : check start292 proof292 = true := by
  decide +kernel

theorem ok293 : check start293 proof293 = true := by
  decide +kernel

theorem ok294 : andB (check start294 proof294) (cpOk (replay start294 proof294) start295) = true := by
  decide +kernel

end Snake9.LocalWindow.SixFour10
