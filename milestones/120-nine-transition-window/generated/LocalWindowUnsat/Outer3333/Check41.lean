import LocalWindowUnsat.Outer3333.Data40
import LocalWindowUnsat.Outer3333.Data41

/-! Kernel checks of segments 41-41 of `outer3333` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Outer3333
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok41 : check start41 proof41 = true := by
  decide +kernel

end Snake9.LocalWindow.Outer3333
