import LocalWindowUnsat.Outer3333.Data51
import LocalWindowUnsat.Outer3333.Data52

/-! Kernel checks of segments 52-52 of `outer3333` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Outer3333
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok52 : andB (check start52 proof52) (cpOk (replay start52 proof52) start53) = true := by
  decide +kernel

end Snake9.LocalWindow.Outer3333
