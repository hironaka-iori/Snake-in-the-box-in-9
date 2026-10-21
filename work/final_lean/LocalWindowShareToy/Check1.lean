import LocalWindowShareToy.Data0
import LocalWindowShareToy.Data1

/-! Kernel checks of segments 1-1 of `share_toy` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareToy
open Snake9.LratFast
open Snake9.LratFast2
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok1 : andB (check2 start1 (perf 5 0) proof1) (hasEmpty (replay start1 proof1) 16) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareToy
