import LocalWindowUnsat.ShareWindow144.Data586
import LocalWindowUnsat.ShareWindow144.Data587

/-! Kernel checks of segments 2341-2344 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok2341 : check start2341 proof2341 = true := by
  decide +kernel

theorem ok2342 : check start2342 proof2342 = true := by
  decide +kernel

theorem ok2343 : check start2343 proof2343 = true := by
  decide +kernel

theorem ok2344 : andB (check start2344 proof2344) (cpOk (replay start2344 proof2344) start2345) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
