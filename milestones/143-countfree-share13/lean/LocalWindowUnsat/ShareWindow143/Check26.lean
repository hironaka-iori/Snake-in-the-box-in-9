import LocalWindowUnsat.ShareWindow143.Data26
import LocalWindowUnsat.ShareWindow143.Data27

/-! Kernel checks of segments 101-104 of `share143` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow143
open Snake9.LratFast143
open Snake9.Lrat143 (Tree TreeTrue andB)

theorem ok101 : check start101 proof101 = true := by
  decide +kernel

theorem ok102 : check start102 proof102 = true := by
  decide +kernel

theorem ok103 : check start103 proof103 = true := by
  decide +kernel

theorem ok104 : andB (check start104 proof104) (cpOk (replay start104 proof104) start105) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow143
