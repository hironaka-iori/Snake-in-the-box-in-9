import LocalWindowUnsat.ShareWindow143.Data66
import LocalWindowUnsat.ShareWindow143.Data67

/-! Kernel checks of segments 261-264 of `share143` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow143
open Snake9.LratFast143
open Snake9.Lrat143 (Tree TreeTrue andB)

theorem ok261 : check start261 proof261 = true := by
  decide +kernel

theorem ok262 : check start262 proof262 = true := by
  decide +kernel

theorem ok263 : check start263 proof263 = true := by
  decide +kernel

theorem ok264 : andB (check start264 proof264) (cpOk (replay start264 proof264) start265) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow143
