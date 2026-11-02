import LocalWindowUnsat.Middle325.Data165
import LocalWindowUnsat.Middle325.Data166

/-! Kernel checks of segments 166-166 of `middle325` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Middle325
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok166 : andB (check start166 proof166) (cpOk (replay start166 proof166) start167) = true := by
  decide +kernel

end Snake9.LocalWindow.Middle325
