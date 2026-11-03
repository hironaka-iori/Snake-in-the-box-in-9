import LocalWindowUnsat.Outer3333.Data24
import LocalWindowUnsat.Outer3333.Data25

/-! Kernel checks of segments 25-25 of `outer3333` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Outer3333
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok25 : check start25 proof25 = true := by
  decide +kernel

end Snake9.LocalWindow.Outer3333
