import LocalWindowUnsat.ShareWindow144.Data76
import LocalWindowUnsat.ShareWindow144.Data77

/-! Kernel checks of segments 301-304 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok301 : check start301 proof301 = true := by
  decide +kernel

theorem ok302 : check start302 proof302 = true := by
  decide +kernel

theorem ok303 : check start303 proof303 = true := by
  decide +kernel

theorem ok304 : andB (check start304 proof304) (cpOk (replay start304 proof304) start305) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
