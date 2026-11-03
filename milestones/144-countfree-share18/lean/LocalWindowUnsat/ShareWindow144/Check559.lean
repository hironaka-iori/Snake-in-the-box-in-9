import LocalWindowUnsat.ShareWindow144.Data559
import LocalWindowUnsat.ShareWindow144.Data560

/-! Kernel checks of segments 2233-2236 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok2233 : check start2233 proof2233 = true := by
  decide +kernel

theorem ok2234 : check start2234 proof2234 = true := by
  decide +kernel

theorem ok2235 : check start2235 proof2235 = true := by
  decide +kernel

theorem ok2236 : andB (check start2236 proof2236) (cpOk (replay start2236 proof2236) start2237) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
