import LocalWindowUnsat.ShareWindow144.Data106
import LocalWindowUnsat.ShareWindow144.Data107

/-! Kernel checks of segments 421-424 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok421 : check start421 proof421 = true := by
  decide +kernel

theorem ok422 : check start422 proof422 = true := by
  decide +kernel

theorem ok423 : check start423 proof423 = true := by
  decide +kernel

theorem ok424 : andB (check start424 proof424) (cpOk (replay start424 proof424) start425) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
