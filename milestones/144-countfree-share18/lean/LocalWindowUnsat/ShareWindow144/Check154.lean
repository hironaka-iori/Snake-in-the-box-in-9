import LocalWindowUnsat.ShareWindow144.Data154
import LocalWindowUnsat.ShareWindow144.Data155

/-! Kernel checks of segments 613-616 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok613 : check start613 proof613 = true := by
  decide +kernel

theorem ok614 : check start614 proof614 = true := by
  decide +kernel

theorem ok615 : check start615 proof615 = true := by
  decide +kernel

theorem ok616 : andB (check start616 proof616) (cpOk (replay start616 proof616) start617) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
