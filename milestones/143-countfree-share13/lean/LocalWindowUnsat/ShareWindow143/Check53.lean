import LocalWindowUnsat.ShareWindow143.Data53
import LocalWindowUnsat.ShareWindow143.Data54

/-! Kernel checks of segments 209-212 of `share143` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow143
open Snake9.LratFast143
open Snake9.Lrat143 (Tree TreeTrue andB)

theorem ok209 : check start209 proof209 = true := by
  decide +kernel

theorem ok210 : check start210 proof210 = true := by
  decide +kernel

theorem ok211 : check start211 proof211 = true := by
  decide +kernel

theorem ok212 : andB (check start212 proof212) (cpOk (replay start212 proof212) start213) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow143
