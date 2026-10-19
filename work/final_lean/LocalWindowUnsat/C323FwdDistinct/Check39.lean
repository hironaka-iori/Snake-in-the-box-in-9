import LocalWindowUnsat.C323FwdDistinct.Data156

/-! Kernel checks of segments 153-156 of `323_fwd_distinct` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.C323FwdDistinct
open Snake9.Lrat

theorem ok153 : andB (check start153 proof153) (cpOk (replay start153 proof153) cp154) = true := by
  decide +kernel

theorem ok154 : check start154 proof154 = true := by
  decide +kernel

theorem ok155 : check start155 proof155 = true := by
  decide +kernel

theorem ok156 : andB (check start156 proof156) (cpOk (replay start156 proof156) cp157) = true := by
  decide +kernel

end Snake9.LocalWindow.C323FwdDistinct
