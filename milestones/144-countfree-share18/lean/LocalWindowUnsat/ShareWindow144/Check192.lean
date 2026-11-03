import LocalWindowUnsat.ShareWindow144.Data192
import LocalWindowUnsat.ShareWindow144.Data193

/-! Kernel checks of segments 765-768 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok765 : check start765 proof765 = true := by
  decide +kernel

theorem ok766 : check start766 proof766 = true := by
  decide +kernel

theorem ok767 : check start767 proof767 = true := by
  decide +kernel

theorem ok768 : andB (check start768 proof768) (cpOk (replay start768 proof768) start769) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
