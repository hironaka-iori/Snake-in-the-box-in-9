import LocalWindowUnsat.ShareWindow144.Data580
import LocalWindowUnsat.ShareWindow144.Data581

/-! Kernel checks of segments 2317-2320 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok2317 : check start2317 proof2317 = true := by
  decide +kernel

theorem ok2318 : check start2318 proof2318 = true := by
  decide +kernel

theorem ok2319 : check start2319 proof2319 = true := by
  decide +kernel

theorem ok2320 : andB (check start2320 proof2320) (cpOk (replay start2320 proof2320) start2321) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
