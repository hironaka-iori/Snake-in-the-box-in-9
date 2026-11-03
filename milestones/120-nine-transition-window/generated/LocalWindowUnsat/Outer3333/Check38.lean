import LocalWindowUnsat.Outer3333.Data37
import LocalWindowUnsat.Outer3333.Data38

/-! Kernel checks of segments 38-38 of `outer3333` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Outer3333
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok38 : andB (check start38 proof38) (cpOk (replay start38 proof38) start39) = true := by
  decide +kernel

end Snake9.LocalWindow.Outer3333
