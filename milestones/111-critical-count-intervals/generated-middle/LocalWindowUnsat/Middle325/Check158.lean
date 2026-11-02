import LocalWindowUnsat.Middle325.Data157
import LocalWindowUnsat.Middle325.Data158

/-! Kernel checks of segments 158-158 of `middle325` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Middle325
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok158 : andB (check start158 proof158) (cpOk (replay start158 proof158) start159) = true := by
  decide +kernel

end Snake9.LocalWindow.Middle325
