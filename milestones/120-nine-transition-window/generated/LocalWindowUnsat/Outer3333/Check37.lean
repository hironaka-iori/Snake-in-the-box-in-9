import LocalWindowUnsat.Outer3333.Data36
import LocalWindowUnsat.Outer3333.Data37

/-! Kernel checks of segments 37-37 of `outer3333` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Outer3333
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok37 : check start37 proof37 = true := by
  decide +kernel

end Snake9.LocalWindow.Outer3333
