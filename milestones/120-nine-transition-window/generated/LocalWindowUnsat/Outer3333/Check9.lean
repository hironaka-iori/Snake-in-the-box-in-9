import LocalWindowUnsat.Outer3333.Data8
import LocalWindowUnsat.Outer3333.Data9

/-! Kernel checks of segments 9-9 of `outer3333` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Outer3333
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok9 : check start9 proof9 = true := by
  decide +kernel

end Snake9.LocalWindow.Outer3333
