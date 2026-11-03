import LocalWindowUnsat.ShareWindow143.Data60
import LocalWindowUnsat.ShareWindow143.Data61

/-! Kernel checks of segments 237-240 of `share143` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow143
open Snake9.LratFast143
open Snake9.Lrat143 (Tree TreeTrue andB)

theorem ok237 : check start237 proof237 = true := by
  decide +kernel

theorem ok238 : check start238 proof238 = true := by
  decide +kernel

theorem ok239 : check start239 proof239 = true := by
  decide +kernel

theorem ok240 : andB (check start240 proof240) (cpOk (replay start240 proof240) start241) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow143
