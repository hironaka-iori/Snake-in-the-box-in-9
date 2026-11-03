import LocalWindowUnsat.ShareWindow144.Data121
import LocalWindowUnsat.ShareWindow144.Data122

/-! Kernel checks of segments 481-484 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok481 : check start481 proof481 = true := by
  decide +kernel

theorem ok482 : check start482 proof482 = true := by
  decide +kernel

theorem ok483 : check start483 proof483 = true := by
  decide +kernel

theorem ok484 : andB (check start484 proof484) (cpOk (replay start484 proof484) start485) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
