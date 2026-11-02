import Recovered108.LocalWindowUnsat.D012304A22623.Data0
import Recovered108.LocalWindowUnsat.D012304A22623.Data1

/-! Kernel checks of segments 1-1 of `d012304_a2_2_6-21_2_3` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.D012304A22623
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok1 : andB (check start1 proof1) (hasEmpty (replay start1 proof1) 64) = true := by
  decide +kernel

end Snake9.LocalWindow.D012304A22623
