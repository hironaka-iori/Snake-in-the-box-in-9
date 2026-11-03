import LocalWindowUnsat.ShareWindow143.Data50
import LocalWindowUnsat.ShareWindow143.Data51

/-! Kernel checks of segments 197-200 of `share143` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow143
open Snake9.LratFast143
open Snake9.Lrat143 (Tree TreeTrue andB)

theorem ok197 : check start197 proof197 = true := by
  decide +kernel

theorem ok198 : check start198 proof198 = true := by
  decide +kernel

theorem ok199 : check start199 proof199 = true := by
  decide +kernel

theorem ok200 : andB (check start200 proof200) (cpOk (replay start200 proof200) start201) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow143
