import LocalWindowUnsat.ShareWindow144.Data595
import LocalWindowUnsat.ShareWindow144.Data596

/-! Kernel checks of segments 2377-2380 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok2377 : check start2377 proof2377 = true := by
  decide +kernel

theorem ok2378 : check start2378 proof2378 = true := by
  decide +kernel

theorem ok2379 : check start2379 proof2379 = true := by
  decide +kernel

theorem ok2380 : andB (check start2380 proof2380) (cpOk (replay start2380 proof2380) start2381) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
