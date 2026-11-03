import LocalWindowUnsat.End44.Data28
import LocalWindowUnsat.End44.Data29

/-! Kernel checks of segments 163-168 of `end44` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.End44
open Snake9.LratFastEndpoint122
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok163 : check start163 proof163 = true := by
  decide +kernel

theorem ok164 : check start164 proof164 = true := by
  decide +kernel

theorem ok165 : check start165 proof165 = true := by
  decide +kernel

theorem ok166 : check start166 proof166 = true := by
  decide +kernel

theorem ok167 : check start167 proof167 = true := by
  decide +kernel

theorem ok168 : andB (check start168 proof168) (cpOk (replay start168 proof168) start169) = true := by
  decide +kernel

end Snake9.LocalWindow.End44
