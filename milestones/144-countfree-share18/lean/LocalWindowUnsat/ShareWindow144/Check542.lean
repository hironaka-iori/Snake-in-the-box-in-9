import LocalWindowUnsat.ShareWindow144.Data542
import LocalWindowUnsat.ShareWindow144.Data543

/-! Kernel checks of segments 2165-2168 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok2165 : check start2165 proof2165 = true := by
  decide +kernel

theorem ok2166 : check start2166 proof2166 = true := by
  decide +kernel

theorem ok2167 : check start2167 proof2167 = true := by
  decide +kernel

theorem ok2168 : andB (check start2168 proof2168) (cpOk (replay start2168 proof2168) start2169) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
