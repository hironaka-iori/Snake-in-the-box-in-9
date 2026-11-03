import LocalWindowUnsat.ShareWindow143.Data23
import LocalWindowUnsat.ShareWindow143.Data24

/-! Kernel checks of segments 89-92 of `share143` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow143
open Snake9.LratFast143
open Snake9.Lrat143 (Tree TreeTrue andB)

theorem ok89 : check start89 proof89 = true := by
  decide +kernel

theorem ok90 : check start90 proof90 = true := by
  decide +kernel

theorem ok91 : check start91 proof91 = true := by
  decide +kernel

theorem ok92 : andB (check start92 proof92) (cpOk (replay start92 proof92) start93) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow143
