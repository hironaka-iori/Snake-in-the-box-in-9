import LocalWindowUnsat.ShareWindow144.Data142
import LocalWindowUnsat.ShareWindow144.Data143

/-! Kernel checks of segments 565-568 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok565 : check start565 proof565 = true := by
  decide +kernel

theorem ok566 : check start566 proof566 = true := by
  decide +kernel

theorem ok567 : check start567 proof567 = true := by
  decide +kernel

theorem ok568 : andB (check start568 proof568) (cpOk (replay start568 proof568) start569) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
