import LocalWindowUnsat.ShareWindow144.Data572
import LocalWindowUnsat.ShareWindow144.Data573

/-! Kernel checks of segments 2285-2288 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok2285 : check start2285 proof2285 = true := by
  decide +kernel

theorem ok2286 : check start2286 proof2286 = true := by
  decide +kernel

theorem ok2287 : check start2287 proof2287 = true := by
  decide +kernel

theorem ok2288 : andB (check start2288 proof2288) (cpOk (replay start2288 proof2288) start2289) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
