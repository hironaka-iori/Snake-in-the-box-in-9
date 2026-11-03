import LocalWindowUnsat.ShareWindow143.Data70

/-! Kernel checks of segments 277-280 of `share143` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow143
open Snake9.LratFast143
open Snake9.Lrat143 (Tree TreeTrue andB)

theorem ok277 : check start277 proof277 = true := by
  decide +kernel

theorem ok278 : check start278 proof278 = true := by
  decide +kernel

theorem ok279 : check start279 proof279 = true := by
  decide +kernel

theorem ok280 : andB (check start280 proof280) (hasEmpty (replay start280 proof280) 8192) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow143
