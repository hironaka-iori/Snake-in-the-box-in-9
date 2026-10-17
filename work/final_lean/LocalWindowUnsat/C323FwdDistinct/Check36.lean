import LocalWindowUnsat.C323FwdDistinct.Data144

/-! Kernel checks of segments 141-144 of `323_fwd_distinct` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.C323FwdDistinct
open Snake9.Lrat

theorem ok141 : andB (check start141 proof141) (cpOk (replay start141 proof141) cp142) = true := by
  decide +kernel

theorem ok142 : check start142 proof142 = true := by
  decide +kernel

theorem ok143 : check start143 proof143 = true := by
  decide +kernel

theorem ok144 : andB (check start144 proof144) (cpOk (replay start144 proof144) cp145) = true := by
  decide +kernel

end Snake9.LocalWindow.C323FwdDistinct
