import LocalWindowUnsat.ShareWindow144.Data594
import LocalWindowUnsat.ShareWindow144.Data595

/-! Kernel checks of segments 2373-2376 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok2373 : check start2373 proof2373 = true := by
  decide +kernel

theorem ok2374 : check start2374 proof2374 = true := by
  decide +kernel

theorem ok2375 : check start2375 proof2375 = true := by
  decide +kernel

theorem ok2376 : andB (check start2376 proof2376) (cpOk (replay start2376 proof2376) start2377) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
