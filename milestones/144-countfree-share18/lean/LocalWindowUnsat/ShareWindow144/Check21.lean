import LocalWindowUnsat.ShareWindow144.Data21
import LocalWindowUnsat.ShareWindow144.Data22

/-! Kernel checks of segments 81-84 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok81 : check start81 proof81 = true := by
  decide +kernel

theorem ok82 : check start82 proof82 = true := by
  decide +kernel

theorem ok83 : check start83 proof83 = true := by
  decide +kernel

theorem ok84 : andB (check start84 proof84) (cpOk (replay start84 proof84) start85) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
