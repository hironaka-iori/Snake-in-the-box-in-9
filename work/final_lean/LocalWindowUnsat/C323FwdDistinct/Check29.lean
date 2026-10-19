import LocalWindowUnsat.C323FwdDistinct.Data116

/-! Kernel checks of segments 113-116 of `323_fwd_distinct` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.C323FwdDistinct
open Snake9.Lrat

theorem ok113 : check start113 proof113 = true := by
  decide +kernel

theorem ok114 : andB (check start114 proof114) (cpOk (replay start114 proof114) cp115) = true := by
  decide +kernel

theorem ok115 : check start115 proof115 = true := by
  decide +kernel

theorem ok116 : check start116 proof116 = true := by
  decide +kernel

end Snake9.LocalWindow.C323FwdDistinct
