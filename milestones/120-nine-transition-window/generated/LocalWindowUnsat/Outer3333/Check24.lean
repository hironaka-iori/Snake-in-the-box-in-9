import LocalWindowUnsat.Outer3333.Data23
import LocalWindowUnsat.Outer3333.Data24

/-! Kernel checks of segments 24-24 of `outer3333` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Outer3333
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok24 : andB (check start24 proof24) (cpOk (replay start24 proof24) start25) = true := by
  decide +kernel

end Snake9.LocalWindow.Outer3333
