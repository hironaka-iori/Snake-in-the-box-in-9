import LocalWindowUnsat.C323FwdDistinct.Data132

/-! Kernel checks of segments 129-132 of `323_fwd_distinct` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.C323FwdDistinct
open Snake9.Lrat

theorem ok129 : andB (check start129 proof129) (cpOk (replay start129 proof129) cp130) = true := by
  decide +kernel

theorem ok130 : check start130 proof130 = true := by
  decide +kernel

theorem ok131 : check start131 proof131 = true := by
  decide +kernel

theorem ok132 : andB (check start132 proof132) (cpOk (replay start132 proof132) cp133) = true := by
  decide +kernel

end Snake9.LocalWindow.C323FwdDistinct
