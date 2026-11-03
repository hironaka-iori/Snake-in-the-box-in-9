import LocalWindowUnsat.ShareWindow144.Data557
import LocalWindowUnsat.ShareWindow144.Data558

/-! Kernel checks of segments 2225-2228 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok2225 : check start2225 proof2225 = true := by
  decide +kernel

theorem ok2226 : check start2226 proof2226 = true := by
  decide +kernel

theorem ok2227 : check start2227 proof2227 = true := by
  decide +kernel

theorem ok2228 : andB (check start2228 proof2228) (cpOk (replay start2228 proof2228) start2229) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
