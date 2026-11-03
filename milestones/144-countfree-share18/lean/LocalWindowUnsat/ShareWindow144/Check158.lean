import LocalWindowUnsat.ShareWindow144.Data158
import LocalWindowUnsat.ShareWindow144.Data159

/-! Kernel checks of segments 629-632 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok629 : check start629 proof629 = true := by
  decide +kernel

theorem ok630 : check start630 proof630 = true := by
  decide +kernel

theorem ok631 : check start631 proof631 = true := by
  decide +kernel

theorem ok632 : andB (check start632 proof632) (cpOk (replay start632 proof632) start633) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
