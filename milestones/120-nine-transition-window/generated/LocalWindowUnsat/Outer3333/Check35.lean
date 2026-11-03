import LocalWindowUnsat.Outer3333.Data34
import LocalWindowUnsat.Outer3333.Data35

/-! Kernel checks of segments 35-35 of `outer3333` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Outer3333
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok35 : check start35 proof35 = true := by
  decide +kernel

end Snake9.LocalWindow.Outer3333
