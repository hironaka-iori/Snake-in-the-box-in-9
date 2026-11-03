import LocalWindowUnsat.ShareWindow143.Data36
import LocalWindowUnsat.ShareWindow143.Data37

/-! Kernel checks of segments 141-144 of `share143` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow143
open Snake9.LratFast143
open Snake9.Lrat143 (Tree TreeTrue andB)

theorem ok141 : check start141 proof141 = true := by
  decide +kernel

theorem ok142 : check start142 proof142 = true := by
  decide +kernel

theorem ok143 : check start143 proof143 = true := by
  decide +kernel

theorem ok144 : andB (check start144 proof144) (cpOk (replay start144 proof144) start145) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow143
