import LocalWindowUnsat.SixFour10.Data60
import LocalWindowUnsat.SixFour10.Data61

/-! Kernel checks of segments 355-360 of `four10` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.SixFour10
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok355 : check start355 proof355 = true := by
  decide +kernel

theorem ok356 : check start356 proof356 = true := by
  decide +kernel

theorem ok357 : check start357 proof357 = true := by
  decide +kernel

theorem ok358 : check start358 proof358 = true := by
  decide +kernel

theorem ok359 : check start359 proof359 = true := by
  decide +kernel

theorem ok360 : andB (check start360 proof360) (cpOk (replay start360 proof360) start361) = true := by
  decide +kernel

end Snake9.LocalWindow.SixFour10
