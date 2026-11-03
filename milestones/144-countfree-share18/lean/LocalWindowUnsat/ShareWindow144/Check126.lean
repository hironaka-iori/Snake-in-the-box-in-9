import LocalWindowUnsat.ShareWindow144.Data126
import LocalWindowUnsat.ShareWindow144.Data127

/-! Kernel checks of segments 501-504 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok501 : check start501 proof501 = true := by
  decide +kernel

theorem ok502 : check start502 proof502 = true := by
  decide +kernel

theorem ok503 : check start503 proof503 = true := by
  decide +kernel

theorem ok504 : andB (check start504 proof504) (cpOk (replay start504 proof504) start505) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
